(ns clojure-metal.emit
  (:refer-clojure :exclude [cast compile])
  (:require [clojure-metal.llvmc :as llvm :refer [gen-name]]
            [clojure-metal.types :as types]
            [clojure-metal.state-monad :refer :all])
  (:import [com.sun.jna Pointer]))


(defn cast [expr tp]
  (gen-plan
   [expr-val expr
    builder (get-in-plan [:builder])]
   (if (= (:ctx expr) :const)
     ((-> tp :cast-from (:type expr) :const) (:value expr))
     ((-> tp :cast-from (:type expr) :builder) builder (:value expr)))))

(defn const-size-t [val]
  (llvm/ConstInt types/size-t val false))

(def const-i1-0 (llvm/ConstInt types/i1 0 false))
(def const-i1-1 (llvm/ConstInt types/i1 1 false))



(def set-function (partial assoc-in-plan [:fn]))
(def get-function (partial get-in-plan [:fn]))


(defn -if [test then else tp]
  (gen-plan
   [f (get-function)
    then-blk (add-block "then")
    else-blk (add-block "else")
    end-blk (add-block "end")

    test-val test
    _ (<-b (llvm/BuildCondBr test-val then-blk else-blk))

    _ (set-block then-blk)
    then-val then
    _ (<-b (llvm/BuildBr end-blk))
    then-end-blk (get-block)

    _ (set-block else-blk)
    else-val else
    _ (<-b (llvm/BuildBr end-blk))
    else-end-blk (get-block)

    _ (set-block end-blk)
    phi (<-b (llvm/BuildPhi tp (gen-name "if_end")))
    _ (<- (llvm/AddIncoming phi
                             (into-array Pointer [then-val else-val])
                             (into-array Pointer [then-end-blk else-end-blk])
                             2))]
   phi))

(defn get-state [x]
  (x {:module (llvm/ModuleCreateWithName (gen-name "module"))
      :builder (llvm/CreateBuilder)}))

(defn add-function [name tp]
  (fn [state]
    {:pre [(:module state)]}
    (let [module (:module state)
          f (llvm/AddFunction module name tp)]
      (llvm/SetFunctionCallConv f llvm/LLVMCCallConv)
      [f state])))

(defn find-function [name]
  (gen-plan
   [module (get-in-plan [:module])
    f (<- (llvm/GetNamedFunction module name))]
   (do (assert f)
       f)))

(defn add-global [name val]
  (println "adding " name)
  (gen-plan
   [module (get-in-plan [:module])
    gbl (<- (llvm/AddGlobal module (llvm/TypeOf val) name))
    _ (<- (llvm/SetInitializer gbl val))
    _ (assoc-in-plan [:known-globals name] {:llvm-type (llvm/TypeOf val)
                                            :llvm-global gbl})]
   gbl))

(defn get-global [name]
  (println "finding " name)
  (gen-plan
   [gbl (get-in-plan [:known-globals name :llvm-global])
    casted (<-b (llvm/BuildBitCast gbl types/i8* name))
    _ (<- (assert gbl))]
   casted))

(defn global-exists? [name]
  (gen-plan
   [gbl (get-in-plan [:known-globals name :llvm-global])]
   gbl))


(defn param [idx]
  (gen-plan
   [f (get-function)]
   (llvm/GetParam f idx)))
