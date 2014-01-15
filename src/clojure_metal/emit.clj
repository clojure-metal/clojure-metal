(ns clojure-metal.emit
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


(defmacro <- [expr]
  "Allows a normal clojure expression to be used in a gen-plan"
  `(fn [state#]
     [~expr state#]))

(defmacro <-b [[first & rest]]
  "Same as <- but assumes that the first arg to the expression will need to be
   replaced with the :builder from the state map"
  `(fn [state#]
     [(~first (:builder state#) ~@rest) state#]))

(def set-function (partial assoc-in-plan [:fn]))
(def get-function (partial get-in-plan [:fn]))


(defn add-block [nm]
  (gen-plan
   [f (get-in-plan [:fn])
    blk (<- (llvm/AppendBasicBlock f (llvm/gen-name nm)))]
   blk))


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



(defn ALIGNMENT []
  (fn [state]
    [(llvm/ConstMul (const-size-t (/ 64 8)) (const-size-t 2)) state]))

(defn ALIGN-CONST
  ;; Aligns a constant int with the alignment
  ;; Formula is:  (((size) + ALIGNMENT - 1) & ~(ALIGNMENT -1))
  [size]
  (gen-plan
   [align (ALIGNMENT)
    a-1 (<- (llvm/ConstSub align (const-size-t 1)))
    s+a-1 (<- (llvm/ConstAdd size a-1))]
   (llvm/ConstAnd s+a-1 (llvm/ConstNot a-1))))

(defn TYPEID [x]
  (gen-plan
   [casted (<-b (llvm/BuildBitCast x (llvm/PointerType types/size-t 0) (gen-name "casted")))
    val (<-b (llvm/BuildLoad casted (gen-name "load")))]
   val))

(defn param [idx]
  (gen-plan
   [f (get-function)]
   (llvm/GetParam f idx)))


(defn do-it []
  (->
   (gen-plan
    [f (add-function "teststuff" (types/function-type [types/i8*] types/size-t))
     _ (set-function f)
     entry (add-block "entry")
     _ (set-block entry)
     a (param 0)
     v (TYPEID a)
     _ (<-b (llvm/BuildRet v))]
    f)
   get-state
   second
   :module
   llvm/dump
   llvm/verify))


(do-it)
