(ns clojure-metal.analyzer
  (:refer-clojure :exclude [cast eval])
  (:require [clojure.core.match :refer [match]]
            [clojure.tools.analyzer :as an]
            [clojure.tools.analyzer.utils :as an-util]
            [clojure.tools.analyzer.ast :as an-ast]))


(defmethod print-method 'clojure.lang.Atom
  [x ^java.io.Writer w]
  (.write w "Atom<>"))

(defn partition-on [pred coll]
  (let [a (atom 0)]
    (partition-by (fn [x]
                    (when (pred x)
                      (swap! a inc))
                    @a) coll)))

(def parse nil)
(defmulti parse (fn [[nm] env]
                  nm))

(defn parse-ctor [[type & args] env]
  {:op :ctor
   :type (symbol (name (:ns env))
                 (subs (name type) 0 (dec (count (name type)))))
   :args (mapv #(an/analyze % env) args)
   :env env})

(def intrinsics '{clojure.metal.native/- 2
                  clojure.metal.native/+ 2
                  clojure.metal.native/< 2})

(defmethod parse :default
  [form env]
  (println "->>>>> form" form)
  (if (and (seq? form)
           (contains? intrinsics (first form)))
    {:op :intrinsic
     :intrinsic (first form)
     :children [:args]
     :args (mapv #(an/analyze % env) (next form))}
    (an/-parse form env)))

(defn add-fn-var [{:keys [ns namespaces] :as env} nm var]
  (let [v (get-in env [ns :mappings nm])]
    (assert (nil? v) (str "Can't re-map var" ns "/" nm))
    (swap! namespaces assoc-in [ns :mappings nm] var)))



(defmethod parse 'deftype
  [[_ name fields & specs] {:keys [ns namespaces] :as env}]
  (let [specs (partition-on symbol? specs)
        typedef {:op :deftype
                 :type-name name
                 :fields fields
                 :field-count (count fields)
                 :children [:protocol-fns]
                 :env env
                 :protocol-fns
                 (vec (for [[proto & methods] specs
                            [nm args & rest :as form] methods]
                        (let [fields-expr (map-indexed
                                           (fn [idx name]
                                             {:op :binding
                                              :local :field
                                              :field-id idx
                                              :fields fields
                                              :field-count (count fields)
                                              :env env
                                              :form name})
                                           fields)
                              menv (assoc env
                                     :locals (zipmap fields fields-expr))
                              resolved (an-util/resolve-var proto env)
                              fn-var  {:op :protocol-fn
                                       :protocol proto
                                       :fn-name nm
                                       :args args
                                       :arg-count (count args)
                                       :children [:body]
                                       :body (an/analyze-fn-method (next form) menv)}]
                          (assert resolved (str "Couldn't resolve protocol " proto))
                          (assert (= (:op resolved) :defprotocol))
                          (assert (get-in resolved [:specs nm (count args)])
                                  (str "Invalid arity for function " nm " in " resolved))
                          fn-var)))}]
    (swap! namespaces assoc-in [ns :mappings name] typedef)
    {:op :void
     :env env}))

(defmethod parse 'defprotocol
  [[_ nm & specs] {:keys [ns namespaces] :as env}]
  (let [specs (reduce
               (fn [acc [name args]]
                 (assoc-in acc [name (count args)] {:args args
                                                    :fixed-arity (count args)})
                 )
               {}
               specs)
        var {:op :defprotocol
             :name (symbol (name (:ns env)) (name nm))
             :specs specs}]
    (swap! namespaces assoc-in [ns :mappings nm] var)
    {:op :void
     :env env}))

(defmethod parse 'defn
  [[_ name & rest] env]
  (let [methods (if (vector? (first rest))
                  [rest]
                  rest)
        methods (mapv #(an/analyze-fn-method % env) methods)
        allowed-arities (set (map :fixed-arity methods))
        var {:op :defn
             :fn-name name
             :allowed-arities allowed-arities
             :children [:methods]
             :env env
             :methods methods}]
    (add-fn-var env name (symbol (clojure.core/name (:ns env))
                                 (clojure.core/name name)))
    var))

(defmethod parse 'loop
  [[_ & rest] env]
  (an/parse (cons 'loop* rest) env))

(defmethod parse 'let
  [[_ & rest] env]
  (an/parse (cons 'let* rest) env))

(defn macroexpand-it [form env]
  (if (seq? form)
    (let [[sym] form]
      (if (= sym 'defn)
        (let [[_ nm & rest] form]
          `(def ~nm (fn* ~@rest)))
        form))
    form))

(defn create-var [nm env]
  {:op :var
   :name nm
   :ns (:ns env)})

(defn analyze
  [form ]
  (binding [an/macroexpand-1 macroexpand-it
            an/create-var    create-var
            an/parse         parse
            an/var?          var?]
    (an/analyze form (an/empty-env))))

(require '[fipp.edn :refer  [pprint IPretty]])

(extend-protocol IPretty
  clojure.lang.Atom
  (-pretty [x]
    [:text "Atom<>"]))


(defn remove-env
  [ast]
  (if (map? ast)
    (dissoc ast :env)
    ast))

(defmulti node->module (fn [state node]
                         (:op node)))

(defmethod node->module :default
  [state node]
  node)

(defn make-full-name
  [ns nm]
  {:pre [ns nm]}
  (symbol (name ns) (name nm)))

(declare run-instructions)

(defprotocol IInvokable
  (invoke [f args globals consts]))

(defprotocol IMathPrimitive
  (math- [this other])
  (math+ [this other])
  (math< [this other]))

(defrecord WBool [true?])

(def WTrue (->WBool true))
(def WFalse (->WBool false))

(defrecord WInteger [value]
  IMathPrimitive
  (math- [this other]
    (->WInteger (- (:value this)
                   (:value other))))
  (math+ [this other]
    (->WInteger (+ (:value this)
                   (:value other))))
  (math< [this other]
    (if (< (:value this)
           (:value other))
      WTrue
      WFalse)))




(defrecord Fn [name methods]
  IInvokable
  (invoke [f args globals consts]
    (let [arity (get methods (count args))]
      (assert arity (str "No arity " (count args) " in " methods))
      (run-instructions  globals consts args (:instructions arity)))))
(defrecord FnMethod [instructions])
(defrecord Module [consts instructions])
(defrecord Def [name value]
  IInvokable
  (invoke [f args globals consts]
    (invoke value args globals consts)))


(defmulti -compile-ast (fn [{:keys [op]} locals]
                         op))

(defn combine-ns-name [ns nm]
  (symbol (name ns) (name nm)))

(defmethod -compile-ast :invoke
  [{:keys [fn args]} locals]
  `[~@(mapcat #(-compile-ast % locals) args)
    ~@(-compile-ast fn locals)
    [:INVOKE ~(count args)]])

(defmethod -compile-ast :do
  [{:keys [statements ret]} locals]
  `[~@(mapcat
       (fn [statement]
         `[~@(-compile-ast statement locals)
           [:POP]])
       statements)
    ~@(-compile-ast ret locals)])

(defmethod -compile-ast :def
  [{:keys [name init env] :as ast} locals]
  `[~@(-compile-ast init locals)
    [:DEF-NS-NAME ~(combine-ns-name (:ns env) name)]])

(defn add-const! [locals value]
  (if-let [id (get-in @locals [:consts value])]
    id
    (do (swap! locals update-in [:consts]
               #(assoc % value (count %)))
        (get-in @locals [:consts value]))))

(defmethod -compile-ast :const
  [{:keys [form type]} locals]
  (let [id (add-const! locals (->WInteger form))]
    [[:CONST id]]))

(defmethod -compile-ast :local
  [{:keys [arg-id]} locals]
  [[:LOAD-ARG arg-id]])

(defmethod -compile-ast :intrinsic
  [{:keys [intrinsic args]} locals]
  (assert (= (count args) (get intrinsics intrinsic))
          (str "Wrong number of args (" (count args) ") given to intrinsic " intrinsic))
   `[~@(mapcat #(-compile-ast % locals) args)
    [:INTRINSIC ~intrinsic]])



(defmethod -compile-ast :maybe-class
  [{:keys [class env]} locals]
  (let [resolved (an-util/resolve-var class env)]
    (assert resolved (str "Cannot resolve " class " in " (:ns env)))
    [[:LOAD-GLOBAL (combine-ns-name (:ns resolved) (:name resolved))]]))

(defmethod -compile-ast :fn
  [{:keys [methods name] :as ast} locals]
  (let [cmethods (->> (for [method methods]
                        (-compile-ast method locals))
                      (into {}))
        const {:methods cmethods
               :name name}
        id (add-const! locals (->Fn name cmethods))]
    [[:CONST id]]))

(defmethod -compile-ast :fn-method
  [{:keys [methods name body fixed-arity] :as ast} locals]
  [fixed-arity (->FnMethod `[~@(-compile-ast body locals)
                             [:RET-VAL]])])


(defmethod -compile-ast :if
  [{:keys [test then else] :as ast} locals]
  (let [testexprs (-compile-ast test locals)
        thenexprs (-compile-ast then locals)
        elseexprs (-compile-ast else locals)]
    `[~@testexprs
      [:JMP-IF-FALSE ~(+ 2 (count thenexprs))]
      ~@thenexprs
      [:JMP ~(inc (count elseexprs))]
      ~@elseexprs]))

(defn compile-ast
  ([ast]
     (compile-ast ast (atom {:consts {}})))
  ([ast locals]
     (map->Module
      (merge
       {:instructions `[~@(-compile-ast ast locals)
                        [:RET-VAL]]}
       (-> @locals
           (update-in [:consts]
                      (fn [mp]
                        (let [inverted (zipmap (vals mp)
                                               (keys mp))]
                          (into [] (for [v (range (count mp))]
                                     (get inverted v)))))))))))


(defn run-instructions [globals consts args instructions]
  (loop [ip 0
         stack ()]
    (let [inst (nth instructions ip)]
      (match inst
             [:CONST idx] (recur (inc ip)
                                 (cons (nth consts idx) stack))

             [:DEF-NS-NAME nm] (let [val (first stack)
                                     var (->Def nm val)]
                                 (swap! globals assoc nm var)
                                 (recur (inc ip) (cons var (next stack))))

             [:POP] (recur (inc ip) (next stack))

             [:INVOKE argc] (let [args (take (inc argc) stack)
                                  retval (invoke (first args) (vec (rest args)) globals consts)
                                  stack (drop (inc argc) stack)]
                              (recur (inc ip)
                                     (cons retval stack)))

             [:LOAD-GLOBAL nm] (recur (inc ip)
                                      (cons (@globals nm) stack))

             [:LOAD-ARG idx] (do (assert (< idx (count args))
                                         (str "arg idx out of range " idx " in " args))
                                 (recur (inc ip)
                                        (cons (nth args idx)
                                              stack)))
             [:RET-VAL] (first stack)

             [:INTRINSIC 'clojure.metal.native/<] (let [retval (math< (first stack)
                                                                      (second stack))]
                                                    (recur (inc ip)
                                                           (->> stack
                                                                next
                                                                next
                                                                (cons retval))))

             [:INTRINSIC 'clojure.metal.native/+] (let [retval (math+ (first stack)
                                                                      (second stack))]
                                                    (recur (inc ip)
                                                           (->> stack
                                                                next
                                                                next
                                                                (cons retval))))

             [:JMP-IF-FALSE a] (if (identical? WFalse (first stack))
                                  (recur (+ ip a)
                                         (next stack))
                                  (recur (inc ip)
                                         (next stack)))
             [:JMP a] (recur (+ ip a)
                             stack)))))

(defn debug [x]
  (clojure.pprint/pprint (an-ast/postwalk x #(if (map? %)
                                               (dissoc % :env)
                                               %)))
  x)

(-> (analyze '(do
                (defn + [x y]
                  (clojure.metal.native/+ x y))
                #_(defn - [x y]
                  (clojure.metal.native/- x y))
                (defn < [x y]
                  (clojure.metal.native/< x y))
                (defn count-up [x max]
                  (if (< x max)
                    (count-up (+ x 1) max)
                    x))
                (count-up 0 1000000)
                #_(defn fib [max]
                  (if (< max 2)
                    max
                    (+ (fib (- max 1))
                       (fib (- max 2)))))
                #_(fib 10)))
    debug
    compile-ast
    debug
    (as-> data
          (let [globals (atom {})]
            (-> (time (run-instructions  globals (:consts data) [] (:instructions data)))
                (vector  @globals)
                (clojure.pprint/pprint)))))
