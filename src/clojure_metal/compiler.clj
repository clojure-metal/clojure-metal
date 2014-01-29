(ns clojure-metal.compiler
  (:refer-clojure :exclude [cast compile])
  (:require [clojure-metal.types :refer :all]
            [clojure-metal.emit :refer :all]
            [clojure-metal.llvmc :as llvm]
            [clojure-metal.targets.target :as target]
            [clojure-metal.analyzer :as analyzer]
            [clojure-metal.primitives :as primitives]
            [clojure-metal.gc :as gc]
            [clojure-metal.state-monad :refer :all])
  (:import [com.sun.jna Pointer]))


(defmulti -emit :op)

(defmethod -emit :fn-method
  [{:keys [] :as ast}]
  (-emit (:body ast)))

(defmethod -emit :do
  [{:keys [statements ret] :as ast}]
  (gen-plan
   [_(all (map -emit statements))
    result (-emit ret)]
   result))

(defmethod -emit :ctor
  [{:keys [type args env]}]
  (gen-plan
   [llvm-type (gc/llvm-type-by-sym type)
    allocd (gc/alloc-amc type)
    casted (<-b (llvm/BuildBitCast allocd (&tp llvm-type) "casted"))
    _ (all (map-indexed
          (fn [idx arg]
            (gen-plan
             [val (-emit arg)
              gep (<-b (llvm/BuildStructGEP casted (inc idx) (str "arg_" idx)))
              _ (<-b (llvm/BuildStore val gep))
              ]
             nil))
          args))]
   allocd))

(defmulti -emit-local :local)

(defmethod -emit-local :field
  [{:keys [fields field-count field-id form]}]
  {:pre [field-id]}
  (let [llvm-type (llvm/StructType (into-array Pointer (concat [size-t]
                                                               (repeat field-count i8*)))
                                   (inc field-count)
                                   false)]
    (gen-plan
     [this (param 0)
      casted (<-b (llvm/BuildBitCast this (&tp llvm-type) "casted"))
      gep (<-b (llvm/BuildStructGEP casted (inc field-id) (str "*" (name form))))
      val (<-b (llvm/BuildLoad gep (str (name form))))
      ]
     val)))

(defmethod -emit-local :let
  [{local-name :name :as ast}]
  (gen-plan
   [locals (get-binding [:locals])]
   (let [l (get locals local-name)]
     (assert l (str "no local " local-name))
     l)))

(defmethod -emit-local :loop
  [{local-name :name :as ast}]
  (gen-plan
   [locals (get-binding [:locals])]
   (let [l (get locals local-name)]
     (assert l (str "no local " local-name))
     l)))

(defmethod -emit-local :arg
  [{:keys [arg-id]}]
  {:pre [(or arg-id)]}
  (gen-plan
   [arg (param arg-id)]
   arg))



(defmethod -emit :binding
  [{:keys [init] bind-name :name :as ast}]
  (gen-plan
   [v (-emit init)
    _ (push-alter-binding [:locals] assoc bind-name v)]
   v))

(defmethod -emit :recur
  [{:keys [exprs] :as ast}]
  (gen-plan
   [vals (all (map -emit exprs))
    this-blk (get-block)
    {:keys [phis block]} (get-binding [:recur-point])
    _ (<- (mapv (fn [phi init]
                  (llvm/AddIncoming phi
                                    (into-array Pointer [init])
                                    (into-array Pointer [this-blk])
                                    1))
                phis vals))
    _ (<-b (llvm/BuildBr block))]
   :terminated))

(defmethod -emit :loop
  [{:keys [bindings body] :as ast}]
  (gen-plan
   [vals (all (map -emit bindings))
    init-blk (get-block)
    loop-end (add-block "loop-end")
    [body-val main-blk] (add-block "loop-body"
                         (gen-plan
                          [phis (all (map #(<-b (llvm/BuildPhi i8* (str (:name %)))) bindings))
                           _ (<- (mapv (fn [phi init]
                                         (llvm/AddIncoming phi
                                                           (into-array Pointer [init])
                                                           (into-array Pointer [init-blk])
                                                           1))
                                       phis vals))
                           _ (push-alter-binding [:locals] merge (zipmap (map :name bindings)
                                                                         phis))
                           this-blk (get-block)
                           _ (push-binding [:recur-point] {:phis phis
                                                           :block this-blk})
                           body-val (-emit body)
                           _ (pop-binding [:locals])
                           _ (if (= body-val :terminated)
                               (no-op)
                               (<-b (llvm/BuildBr loop-end)))]
                          body-val))
    _ (<-b (llvm/BuildBr main-blk))
    _ (all (repeat (count bindings) (pop-binding :locals)))
    _ (if (= body-val :terminated)
        (<- (llvm/DeleteBasicBlock loop-end))
        (set-block loop-end))]
   body-val))

(defmethod -emit :let
  [{:keys [bindings body] :as ast}]
  (gen-plan
   [vals (all (map -emit bindings))
    val (-emit body)
    _ (all (repeat (count bindings) (pop-binding :locals)))]
   val))

(defmulti -emit-const :type)

(defmethod -emit-const :nil
  [ast]
  (primitives/const-nil))

(defmethod -emit-const :number
  [{:keys [val]}]
  (cond
   (integer? val) (primitives/const-int val)
   :else (assert false)))

(defmethod -emit :const
  [{:keys [] :as ast}]
  (-emit-const ast))

(defmethod -emit :local
  [{:keys [arg-id field-id] :as ast}]
  (-emit-local ast))

(defmethod -emit :defn
  [{:keys [fn-name env fn-methods]}]
  (let [ns (:ns env)]
    (println (keys (first fn-methods)))
    (all (for [{:keys [fixed-arity body]} fn-methods
               :let [full-name (str ns "." fn-name "_" fixed-arity)]]
           (gen-plan
            [f (add-function full-name
                             (function-type (repeat fixed-arity i8*) i8*))
             _ (assoc-in-plan [:known-fns full-name]
                              {:llvm-fn f
                               :gen-body
                               (gen-plan [_ (set-function f)

                                          entry-blk (add-block "entry")
                                          _ (set-block entry-blk)
                                          result (-emit body)
                                          _ (<- (println result))
                                          _ (if-not (= result :terminated)
                                              (<-b (llvm/BuildRet result))
                                              (no-op))]
                                         nil)})]
            nil)))))

(defmulti -emit-invoke (fn [{:keys [op] :as f} args]
                         op))

(defmethod -emit-invoke :maybe-class
  [{:keys [class env]} args]
  (let [fn-name (str (:ns env) "." class "_" (count args))]
    (gen-plan
     [f (find-function fn-name)
      args (all (map -emit args))
      result (<-b (llvm/BuildCall f (into-array Pointer args) (count args) "call"))]
     result)))

(defmethod -emit :invoke
  [{:keys [args] fn-name :fn :as ast}]
  (-emit-invoke fn-name args))

(defn build-fn-bodies []
  (gen-plan
   [known-fns (get-in-plan [:known-fns])
    _ (all (for [[_ {:keys [gen-body]}] known-fns]
             gen-body))]
   nil))

(defmethod -emit :deftype
  [{:keys [fields type-name env fields field-count protocol-fns]}]
  {:pre [(number? field-count)]}
  (let [llvm-type (llvm/StructType (into-array Pointer (concat [size-t]
                                                               (repeat field-count i8*)))
                              (inc field-count)
                              false)]
    (gen-plan
     [tid (gc/gen-typeid)
      _ (assoc-in-plan [:known-types (name (:ns env)) (name type-name)] {:type-id tid
                                                                         :llvm-type llvm-type})
      _ (assoc-in-plan [:known-types (name (:ns env)) (name type-name) :fns]
                       {::gc/size (fn [base]
                                    (gen-plan
                                     []
                                     (const-size-t (* (inc field-count) *size-t-bytes*))))
                        ::gc/scan (fn [base]
                                    (gen-plan
                                     [casted (<-b (llvm/BuildBitCast base (&tp llvm-type) "casted"))
                                      _ (all (for [offset (range field-count)]
                                               (gen-plan
                                                [gep (<-b (llvm/BuildStructGEP casted
                                                                               (inc offset)
                                                                               (name (nth fields offset))))
                                                 _ (gc/FIX gep)]
                                                nil
                                                )))]
                                     nil))})
      _ (all (for [{:keys [fn-name arg-count args body]} protocol-fns]
               (assoc-in-plan [:known-proto-fns fn-name arg-count tid]
                              {:body-fn (-emit body)
                               :type-name (str (name (:ns env)) (name type-name))})))]
     nil)))

(defn generate-function-name [ns-name fn-name arity]
  (str "fn_" ns-name "." fn-name "_" arity))

(defn generate-proto-fn-body [fn-name arity impls]
  (gen-plan
   [f (add-function (generate-function-name "tmp" fn-name arity)
                    (function-type (repeat arity i8*) i8*))
    _ (set-function f)

    entry-blk (add-block "entry")
    _ (set-block entry-blk)
    arg0 (param 0)
    type-id (gc/TYPEID arg0)
    results (all (for [[tid {:keys [type-name body-fn]}] impls]
                   (->> (gen-plan
                         [val body-fn
                          _ (<-b (llvm/BuildRet val))]
                         tid)
                        (add-block type-name))))

    [_ else-blk] (add-block "fail" (<-b (llvm/BuildRet arg0)))

    switch (<-b (llvm/BuildSwitch type-id else-blk (count results)))
    _ (all (for [[type-id block] results]
             (<- (llvm/AddCase switch (const-size-t type-id) block))))]
   nil))


(defn generate-polymorphic-bodies []
  (gen-plan
   [known-proto-fns (get-in-plan [:known-proto-fns])
    _ (<- (println "protofns " known-proto-fns))
    _ (all (for [[fn-name arities] known-proto-fns
                 [arity impls] arities]
             (generate-proto-fn-body fn-name arity impls)))]
   nil))



(def default-target-fn (atom nil))

(defn default-target []
  (require 'clojure-metal.targets.darwin)
  (let [init (intern 'clojure-metal.targets.darwin 'init-target)]
    (init (fn [d-fn]
              (reset! default-target-fn d-fn)))
    (@default-target-fn)))

(defn compile [form]
  (let [ast (analyzer/analyze form)
        module (->(gen-plan
                   [_ (gc/add-gc)
                    _ (primitives/add-pimitives)
                    _ (-emit ast)
                    _ (gc/generate-gc-fns)
                    _ (generate-polymorphic-bodies)
                    _ (build-fn-bodies)
                    f (find-function "user.-main_0")
                    _ (gc/main
                       (gen-plan
                        [_ (<-b (llvm/BuildCall f (into-array Pointer []) 0 "result"))]
                        nil))]
                   nil)
                  get-state
                  second
                  :module
                  llvm/dump
                  llvm/verify
                  llvm/optimize
                  llvm/dump
                  llvm/verify
                  )]
    (target/emit-to-file (default-target) module {:filename "out.s"
                                                      :obj-type :asm})))

(compile '(do (deftype Cons [head tail meta]
                ISeq
                (seq [this] tail)
                (first [this] head)
                (next [this] tail)
                IMeta
                (meta [this] meta)
                (with-meta [this meta]
                  (Cons. head tail meta)))

              (defn cons [x o]
                (Cons. x o nil))

              (defn -main []

                (loop [x nil]

                  (recur (cons 1 x))))))
