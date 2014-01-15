(ns clojure-metal.types
  (:require [clojure-metal.llvmc :as llvm]
            [clojure-metal.state-monad :refer :all])
  (:import [com.sun.jna Pointer]))

(def ^:dynamic size-t (llvm/IntType 64))
(def ^:dynamic *size-t-bytes* 8)

(def i8* (llvm/PointerType (llvm/IntType 8) 0))

(def i1 (llvm/IntType 1))

(defn function-type [args ret-type]
  (llvm/FunctionType ret-type
                     (into-array Pointer args)
                     (count args)
                     false))

(defmacro defllvmstruct
  [tp members]
  (let [parted (partition 2 members)]
    `(do
       (def ~tp (llvm/StructType (into-array Pointer ~(vec (map first parted)))
                                 ~(count parted)
                                 false))
       ~@(map-indexed
          (fn [idx [member-tp nm]]
            `(do (defn ~(symbol (str (name tp) "->" (name nm)))
                   [ptr#]
                   (gen-plan
                    [casted# (<-b (llvm/BuildBitCast ptr# (llvm/PointerType ~tp 0)))
                     v# (<-b (llvm/BuildStructGEP casted# ~idx (llvm/gen-name ~(str (name tp) "->" (name nm)))))]
                    v#))
                 (defn ~(symbol (str (name tp) "->" (name nm) "="))
                   [ptr# val#]
                   (gen-plan
                    [gep# (<-b (llvm/BuildStructGEP ptr# ~idx (llvm/gen-name "gep")))
                     _# (<-b (llvm/BuildStore val# gep#))]
                    gep#))
                 (defn ~(symbol (str "=" (name tp) "->" (name nm)))
                   [ptr#]
                   (gen-plan
                    [casted# (<-b (llvm/BuildBitCast ptr# (llvm/PointerType ~tp 0) "casted"))
                     gep# (<-b (llvm/BuildStructGEP casted# ~idx "gep"))
                     val# (<-b (llvm/BuildLoad gep# "gep_load"))]
                    val#))
                 (defn ~(symbol (str "x=" (name tp) "->" (name nm)))
                   [x# ptr#]
                   (gen-plan
                    [casted# (<-b (llvm/BuildBitCast ptr# (llvm/PointerType ~tp 0)))
                     gep# (<-b (llvm/BuildStructGEP casted# ~idx (llvm/gen-name "gep")))
                     val# (<-b (llvm/BuildLoad gep# ~(name nm)))
                     _# (<-b (llvm/BuildStore val# x#))]
                    val#))
                 (defn ~(symbol (str (name tp) "->" (name nm) "=x"))
                   [ptr# x#]
                   (gen-plan
                    [casted# (<-b (llvm/BuildBitCast ptr# (llvm/PointerType ~tp 0) "casted"))
                     gep# (<-b (llvm/BuildStructGEP casted# ~idx (llvm/gen-name "gep")))
                     val# (<-b (llvm/BuildLoad x# ~(name nm)))
                     _# (<-b (llvm/BuildStore val# gep#))]
                    val#))))

          parted))))
