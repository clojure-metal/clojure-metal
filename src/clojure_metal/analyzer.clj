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

(defmethod parse :default
  [form env]
  (an/-parse form env))

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
              {:op :protocol-fn
               :protocol proto
               :name nm
               :args args
               :arg-count (count args)
               :children [:body]
               :body (an/analyze-fn-method (next form) env)}))}))

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
