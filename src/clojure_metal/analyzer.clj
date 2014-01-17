(ns clojure-metal.analyzer
  (:refer-clojure :exclude [cast])
  (:require [clojure.tools.analyzer :as an]))

(defn partition-on [pred coll]
  (let [a (atom 0)]
    (partition-by (fn [x]
                    (when (pred x)
                      (swap! a inc))
                    @a) coll)))

(defmulti parse (fn [[nm] env]
                  nm))

(defn parse-ctor [[type & args] env]
  {:op :ctor
   :type (symbol (name (:ns env))
                 (subs (name type) 0 (dec (count (name type)))))
   :args (mapv #(an/analyze % env) args)
   :env env})

(defmethod parse :default
  [form env]
  (println "fmr " form)
  (if (and (seq? form)
           (symbol? (first form))
           (.endsWith (name (first form)) "."))
    (parse-ctor form env)
    (an/-parse form env)))

(defmethod parse 'deftype
  [[_ name fields & specs] env]
  (let [specs (partition-on symbol? specs)]
    {:op :deftype
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
                        :locals (zipmap fields fields-expr))]
              {:op :protocol-fn
               :protocol proto
               :fn-name nm
               :args args
               :arg-count (count args)
               :children [:body]
               :body (an/analyze-fn-method (next form) menv)})))}))

(defmethod parse 'defn
  [[_ name & rest] env]
  (let [methods (if (vector? (first rest))
                  [rest]
                  rest)]
    {:op :defn
     :fn-name name
     :env env
     :fn-methods (mapv #(an/analyze-fn-method % env) methods)}))

(defmethod parse 'loop
  [[_ & rest] env]
  (an/parse (cons 'loop* rest) env))

(defmethod parse 'let
  [[_ & rest] env]
  (an/parse (cons 'let* rest) env))

(defn macroexpand-it [x y]
  (println "macro " x)
  x)

(defn create-var [x]
  (println "create-var" x)
  x)

(defn analyze
  [form ]
  (binding [an/macroexpand-1 macroexpand-it
            an/create-var    create-var
            an/parse         parse
            an/var?          var?]
    (an/analyze form (an/empty-env))))
