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

(def mps_ss (llvm/StructType (into-array Pointer [size-t size-t size-t])
                             3
                             false))

(defmacro make-member-accessors
  [tp members]
  (let [parted (partition 2 members)]
    `(do
       (def ~tp (llvm/StructType (into-array Pointer ~(vec (map first parted)))
                                 ~(count members)
                                 false))
       ~@(map-indexed
          (fn [idx [member-tp nm]]
            `(do (defn ~(symbol (str (name tp) "->" (name nm)))
                   [ptr#]
                   (gen-plan
                    [v (<-b (llvm/BuildStructGEP ptr# ~idx (llvm/gen-name "gep")))]
                    v))
                 (defn ~(symbol (str (name tp) "->" (name nm) "="))
                   [ptr# val#]
                   (gen-plan
                    [gep (<-b (llvm/BuildStructGEP ptr# ~idx (llvm/gen-name "gep")))
                     _ (<-b (llvm/BuildStore val# gep))]
                    gep))
                 (defn ~(symbol (str "=" (name tp) "->" (name nm)))
                   [ptr#]
                   (gen-plan
                    [gep (<-b (llvm/BuildStructGEP ptr# ~idx (llvm/gen-name "gep")))
                     val (<- (llvm/BuildLoad gep "gep_load"))]
                    val))))

          parted))))

(clojure.pprint/pprint (macroexpand '
                        (make-member-accessors mps_ss_t
                                               [size-t zs
                                                size-t w
                                                size-t ufs])))


(gen-plan
 [_mps_zs (=mps_ss_t->_zs ss)
  _mps_w (=mps)])


(defn MPS_BEGIN [ss]
  (gen-plan
   [casted (<-b (llvm/BuildBitCast ss mps_ss_t "casted"))
    _mps_zs (<-b (llvm/BuildAlloca size-t))
    _mps_w (<-b (llvm/BuildAlloca size-t))
    _mps_ufs (<-b (llvm/BuildAlloca size-t))
    _mps_wt (<-b (llvm/BuildAlloca size-t))

    _ (assoc-in-plan [:gc :scan] {:_mps_zs _mps_zs
                                  :_mps_w _mps_w
                                  :_mps_ufs _mps_ufs
                                  :_mps_wt _mps_wt})]))

;; _mps_wt = (mps_word_t)1 << ((size_t)(ref) >> _mps_zs & (sizeof(mps_word_t) * CHAR_BIT - 1))
;; _mps_ufs |= _mps_wt,
;; (_mps_w & _mps_wt) != 0

(defn MPS_FIX1 [ref]
  (gen-plan
   [_mps_wd (get-in-plan [:gc :scan :_mps_wd])
    _mps_ufs (get-in-plan [:gc :scan :_mps_ufs])
    _mps_wt (get-in-plan [:gc :scan :_mps_wt])
    _mps_w (get-in-plan [:gc :scan :_mps_w])
    _mps_zs (get-in-plan [:gc :scan :_mps_zs])

    ;; _mps_wt = (mps_word_t)1 << ((size_t)(ref) >> _mps_zs & (sizeof(mps_word_t) * CHAR_BIT - 1))
    rh (<- (* *size-t-bytes* 7)) ;; (sizeof(mps_word_t) * CHAR_BIT - 1)
    *_mps_zs (<- (llvm/BuildLoad _mps_zs "_mps_zs"))
    *ref (<-b (llvm/BuildLoad ref "*ref"))
    ref-size-t (<- (llvm/BuildPtrToInt *ref size-t "refi"))
    mid (<-b (llvm/BuildShr ref-size-t *_mps_zs)) ;; ((size_t)(ref) >> _mps_zs)
    right (<-b (llvm/BuildAnd mid rh "anded"))
    _mps_wt_new (<-b (llvm/BuildShl (const-size-t 1) right "1 << right"))
    _ (<-b (llvm/BuildStore _mps_wt_new _mps_wt))

    ;; _mps_ufs |= _mps_wt,
    *_mps_ufs (<-b (llvm/BuildLoad _mps_ufs "_mps_ufs"))
    _mps_ufs_new (<-b (llvm/BuildOr *_mps_ufs _mps_wt_new))
    _ (<-b (llvm/BuildStore _mps_ufs_new _mps_ufs))

    ;; (_mps_w & _mps_wt) != 0
    *_mps_w (<-b (llvm/BuildLoad _mps_w "_mps_w"))
    anded (<-b (llvm/BuildAnd _mps_w _mps_wt_new "anded"))
    zero? (<-b (llvm/BuildICmp llvm/IntEQ resut (const-size-t 0)))]
   zero?))

(defn MPS_FIX12 [ss ref_io]
  (gen-plan
   [module (get-in-plan [:module])
    _mps_fix2 (llvm/GetNamedFunction module "_mps_fix2")
    fix1-result (MPS_FIX1 ref_io)
    if-result (-if fix1-result
                   (<-b (llvm/BuildCall _mps_fix2 (into-array Pointer [ss ref-io]) 2))
                   (const-size-t 0))]
   if-result))

(defn FIX
  "_addr should be a gep "
  [gep]
  (gen-plan
   [_addr (<-b (llvm/BuildAlloca i8* "_addr"))
    _ (<-b (llvm/BuildStore gep _addr))
    result (MPS_FIX12 ss _addr)
    zero? (<-b (llvm/BuildICmp llvm/IntEQ resut (const-size-t 0)))
    continue-block (add-block)
    _ (<-b (LLVM/BuildCondBr zero? continue-block exit-block)
    addr-val (<- (llvm/BuildLoad _addr "_addr-val"))
    _ (<-b (llvm/BuildStore addr-val gep)))]))

(gen-plan
 [_ (FIX mps_ss_t->_sz)])


(loop [_zs =mps_ss_t->_zs
       _w =mps_ss_t->_w
       _ufs =mps_ss_t->_ufs
       _wt 0]
  )
