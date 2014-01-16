(ns clojure-metal.compiler
  (:refer-clojure :exclude [cast compile])
  (:require [clojure-metal.types :refer :all]
            [clojure-metal.emit :refer :all]
            [clojure-metal.llvmc :as llvm]
            [clojure-metal.analyzer :as analyzer]
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

(defmethod -emit :local
  [{:keys [arg-id] :as ast}]
  {:pre [arg-id]}
  (gen-plan
   [arg (param arg-id)]
   arg))

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
                                                                         :llvm-type type})
      _ (assoc-in-plan [:known-types (name (:ns env)) (name type-name) :fns]
                       {::gc/size (fn [base]
                                    (gen-plan
                                     []
                                     (const-size-t (* (inc field-count) *size-t-bytes*))))
                        ::gc/scan (fn [base]
                                    (gen-plan
                                     [casted (<-b (llvm/BuildBitCast base (&tp llvm-type)))
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
  (str "fn_" + ns-name "." fn-name "_" arity))

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



(defn compile [form]
  (let [ast (analyzer/analyze form)]
    (-> (gen-plan
         [_ (gc/add-gc)
          _ (-emit ast)
          _ (gc/generate-gc-fns)
          _ (generate-polymorphic-bodies)]
         nil)
        get-state
        second
        :module
        llvm/dump)))

(compile '(do (deftype foo [x y]
                IBar
                (baz [x] x)
                (baz [x y] y))
              (deftype baz [x]
                IBar
                (baz [x y] x))))
