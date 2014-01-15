(ns clojure-metal.types
  (:require [clojure-metal.llvmc :as llvm])
  (:import [com.sun.jna Pointer]))

(def ^:dynamic size-t (llvm/IntType 64))

(def i8* (llvm/PointerType (llvm/IntType 8) 0))

(def i1 (llvm/IntType 1))

(defn function-type [args ret-type]
  (llvm/FunctionType ret-type
                     (into-array Pointer args)
                     (count args)
                     false))
