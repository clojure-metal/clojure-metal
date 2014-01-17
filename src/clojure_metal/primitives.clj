(ns clojure-metal.primitives
  (:refer-clojure :exclude [cast compile])
  (:require [clojure-metal.types :refer :all]
            [clojure-metal.emit :refer :all]
            [clojure-metal.llvmc :as llvm]
            [clojure-metal.analyzer :as analyzer]
            [clojure-metal.gc :as gc]
            [clojure-metal.state-monad :refer :all])
  (:import [com.sun.jna Pointer]))

(def primitive-global-prefix "_cm_prim_global_")

(defn add-pimitives []
  (gen-plan
   [nil-tid (gc/gen-typeid)
    nil-data (<- (llvm/ConstStruct (into-array Pointer [(const-size-t nil-tid)]) 1 false))
    nil-gbl (add-global (str primitive-global-prefix "nil") nil-data)

    int-tid (gc/gen-typeid)
    _ (assoc-in-plan [:known-types :clojure-metal.primitives :int]
                     {:type-id int-tid
                      :fns {::gc/size (fn [base]
                                        (<- (const-size-t (* *size-t-bytes* 2))))}})]
   nil-gbl))

(defn const-nil []
  (get-global (str primitive-global-prefix "nil")))


(defn const-int [x]
  {:pre [(integer? x)]}
  (let [nm (str primitive-global-prefix "int" "_" x)]
    (gen-plan
     [maybe-global (global-exists? nm)

      gbl (if maybe-global
            maybe-global
            (gen-plan
             [int-tid (get-in-plan [:known-types :clojure-metal.primitives :int :type-id])
              int-data (<- (llvm/ConstStruct (into-array Pointer
                                                         [(const-size-t int-tid)
                                                          (llvm/ConstInt (llvm/IntType *size-t-bytes*)
                                                                         x
                                                                         true)])
                                             2
                                             false))
              gbl (add-global nm int-data)
              gbl (get-global nm)]
             gbl))]
     gbl)))
