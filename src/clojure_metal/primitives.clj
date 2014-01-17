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
    nil-gbl (add-global (str primitive-global-prefix "nil")
                    (llvm/StructType (into-array Pointer [size-t]) 1 false)
                    nil-data)]
   nil-gbl))

(defn const-nil []
  (get-global (str primitive-global-prefix "nil")))
