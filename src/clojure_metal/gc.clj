(ns clojure-metal.gc
  (:refer-clojure :exclude [cast])
  (:require [clojure-metal.types :refer :all]
            [clojure-metal.emit :refer :all]
            [clojure-metal.llvmc :as llvm]
            [clojure-metal.state-monad :refer :all])
  (:import [com.sun.jna Pointer]))

(defn ALIGNMENT []
  (fn [state]
    [(const-size-t (* 2  *size-t-bytes*)) state]))

(defn ALIGN-CONST
  ;; Aligns a constant int with the alignment
  ;; Formula is:  (((size) + ALIGNMENT - 1) & ~(ALIGNMENT -1))
  [size]
  (gen-plan
   [align (ALIGNMENT)
    a-1 (<- (llvm/ConstSub align (const-size-t 1)))
    s+a-1 (<- (llvm/ConstAdd size a-1))]
   (llvm/ConstAnd s+a-1 (llvm/ConstNot a-1))))

(defn ALIGN-VAL
  [size]
  (gen-plan
   [builder (get-in-plan [:builder])
    align (ALIGNMENT)
    a-1 (<-b (llvm/BuildSub align (const-size-t 1) "sub"))
    s+a-1 (<-b (llvm/BuildAdd size a-1 "add"))]
   (llvm/BuildAnd builder s+a-1 (llvm/BuildNot builder a-1 "not") "aligned")))

(defn TYPEID [x]
  (gen-plan
   [casted (<-b (llvm/BuildBitCast x (llvm/PointerType size-t 0) "casted"))
    val (<-b (llvm/BuildLoad casted "loaded"))]
   val))


(defllvmstruct mps_ss_t [size-t _zs
                         size-t _w
                         size-t _ufs])

(defn MPS_BEGIN [ss]
  {:pre [ss mps_ss_t]}
  (gen-plan
   [casted (<-b (llvm/BuildBitCast ss (llvm/PointerType mps_ss_t 0) "casted"))
    _mps_zs (<-b (llvm/BuildAlloca size-t "_mps_zs"))
    _mps_w (<-b (llvm/BuildAlloca size-t "_mps_w"))
    _mps_ufs (<-b (llvm/BuildAlloca size-t "_mps_ufs"))
    _mps_wt (<-b (llvm/BuildAlloca size-t "_mps_wt"))

    _ (x=mps_ss_t->_zs _mps_zs casted)
    _ (x=mps_ss_t->_w _mps_w casted)
    _ (x=mps_ss_t->_ufs _mps_ufs casted)

    _ (<-b (llvm/BuildStore (const-size-t 0) _mps_wt))


    exit-block (add-block "exit_block")
    old-block (get-block)
    _ (set-block exit-block)
    exit-phi (<-b (llvm/BuildPhi size-t "exit"))
    _ (<-b (llvm/BuildRet exit-phi))


    _ (set-block old-block)


    _ (assoc-in-plan [:gc :scan] {:_mps_zs _mps_zs
                                :_mps_w _mps_w
                                :_mps_ufs _mps_ufs
                                :_mps_wt _mps_wt
                                :ss ss
                                :exit-phi exit-phi
                                :exit-block exit-block
                                })]
   nil))

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
    rh (<- (const-size-t (* *size-t-bytes* 7))) ;; (sizeof(mps_word_t) * CHAR_BIT - 1)
    *_mps_zs (<-b (llvm/BuildLoad _mps_zs "*_mps_zs"))
    *ref (<-b (llvm/BuildLoad ref "*ref"))
    ref-size-t (<-b (llvm/BuildPtrToInt *ref size-t "refi"))
    mid (<-b (llvm/BuildLShr ref-size-t *_mps_zs "mid")) ;; ((size_t)(ref) >> _mps_zs)

    right (<-b (llvm/BuildAnd mid rh "right"))
  _mps_wt_new (<-b (llvm/BuildShl (const-size-t 1) right "_mps_wt_new"))
_ (<-b (llvm/BuildStore _mps_wt_new _mps_wt))

        ;; _mps_ufs |= _mps_wt,
    *_mps_ufs (<-b (llvm/BuildLoad _mps_ufs "_mps_ufs"))
    _mps_ufs_new (<-b (llvm/BuildOr *_mps_ufs _mps_wt_new "|="))
    _ (<-b (llvm/BuildStore _mps_ufs_new _mps_ufs))

    ;; (_mps_w & _mps_wt) != 0
    *_mps_w (<-b (llvm/BuildLoad _mps_w "_mps_w"))
    anded (<-b (llvm/BuildAnd *_mps_w _mps_wt_new "anded"))
    zero? (<-b (llvm/BuildICmp llvm/LLVMIntEQ anded (const-size-t 0) "zero?"))]
   zero?))

(defn MPS_FIX12 [ss ref-io]
  (gen-plan
   [module (get-in-plan [:module])
    fix1-result (MPS_FIX1 ref-io)
    _mps_fix2 (<- (llvm/GetNamedFunction module "_mps_fix2"))
    if-result (-if (<- fix1-result)
                   (<-b (llvm/BuildCall _mps_fix2 (into-array Pointer [ss ref-io]) 2 "_mps_fix2"))
                   (<- (const-size-t 0))
                   size-t)
    _ (<- (assert _mps_fix2))]
   if-result))


(defn FIX
  "_addr should be a gep "
  [gep]
  (gen-plan
   [ss (get-in-plan [:gc :scan :ss])
    exit-block (get-in-plan [:gc :scan :exit-block])
    exit-phi (get-in-plan [:gc :scan :exit-phi])
    _ (<- (assert (and exit-block exit-phi)))

    _addr (<-b (llvm/BuildAlloca i8* "_addr"))
    _ptr (<-b (llvm/BuildLoad gep "_ptr"))
    _ (<-b (llvm/BuildStore _ptr _addr))
    result (MPS_FIX12 ss _addr)
    zero? (<-b (llvm/BuildICmp llvm/LLVMIntEQ result (const-size-t 0) "zero?"))

    this-block (get-block)
    continue-block (add-block "continue")
    _ (<-b (llvm/BuildCondBr zero? continue-block exit-block))

    _ (set-block continue-block)
    _ (<- (llvm/AddIncoming exit-phi
                            (into-array Pointer [result])
                            (into-array Pointer [this-block])
                            1))
    addr-val (<-b (llvm/BuildLoad _addr "_addr-val"))
    _ (<-b (llvm/BuildStore addr-val gep))]
   nil))

(defn MPS_SCAN_END []
  (gen-plan
   [ss (get-in-plan [:gc :scan :ss])
    _mps_ufs (get-in-plan [:gc :scan :_mps_ufs])
    _ (mps_ss_t->_ufs=x ss _mps_ufs)]
   nil))


(defn add-externals []
  (gen-plan
   [_mps_fix2 (add-function "_mps_fix2" (function-type [i8* (llvm/PointerType i8* 0)] size-t))]
   nil))

(defmacro defapptype [nm members & {:as fns}]
  `(do (defllvmstruct ~nm ~members)
       (let [ns-name# (.getName *ns*)]
         (def ~(symbol (str "def-" (name nm)))
           (gen-plan
            [_# (update-in-plan [:next-type-id]  (fnil inc -1))
             tid# (get-in-plan [:next-type-id])
             _# (assoc-in-plan [:known-types (name ns-name#) ~(name nm) :fns] ~fns)
             _# (assoc-in-plan [:known-types (name ns-name#) ~(name nm) :type-id] tid#)]
            nil)))))


(defapptype fwd_t [size-t tid
                   i8* new-loc
                   size-t size]
  :clojure-metal.gc/size (fn [base]
                           (gen-plan
                            [size (=fwd_t->size base)]
                            size))
  :clojure-metal.gc/fwd (fn [base]
                          (gen-plan
                           [fwd (fwd_t->new-loc)]
                           fwd)))

(defapptype fwd_small_t [size-t tid
                   i8* new-loc]
  :clojure-metal.gc/size (fn [base]
                           (gen-plan
                            []
                            (const-size-t (* 2 *size-t-bytes*))))
  :clojure-metal.gc/fwd (fn [base]
                          (gen-plan
                           [fwd (fwd_small_t->new-loc)]
                           fwd)))

(defapptype pad_t [size-t tid
                   size-t size]
  :clojure-metal.gc/size (fn [base]
                           (gen-plan
                            [size (=pad_t->size base)]
                            size)))

(defapptype cons_t [size-t tid
                    i8* head
                    i8* tail]
  :clojure-metal.gc/size (fn [base]
                           (gen-plan
                            []
                            (const-size-t (* 3 *size-t-bytes*))))
  :clojure-metal.gc/scan (fn [base]
                           (gen-plan
                            [gep (cons_t->head base)
                             _ (FIX gep)

                             gep (cons_t->tail base)
                             _ (FIX gep)]
                            nil)))


(defn when-typeid [[val id] body]
  (gen-plan
   [cmp (<-b (llvm/BuildICmp llvm/LLVMIntEQ val id (str "typecheck")))
    then-blk (add-block "then-block")
    continue-blk (add-block "continue-blk")
    _ (<-b (llvm/BuildCondBr cmp then-blk continue-blk))
    _ (set-block then-blk)

    _ body

    _ (<-b (llvm/BuildBr continue-blk))

    _ (set-block continue-blk)]
   nil))

(defn make-obj-scan-body [ns-name tp-name {:keys [type-id fns] :as tpmap}]
  (let [mk-size (::size fns)
        mk-scan (::scan fns)]
    (gen-plan
     [block (add-block (str ns-name "." tp-name))

      old-block (get-block)
      _ (set-block block)

      base (get-in-plan [:gc :base])
      *base (<-b (llvm/BuildLoad base "*base"))
      _ (if mk-scan
          (mk-scan *base)
          (no-op))

      base_i (<-b (llvm/BuildPtrToInt *base size-t "base_i"))
      size (mk-size *base)
      size (ALIGN-VAL size)
      base+size (<-b (llvm/BuildAdd base_i size "base+size"))
      _ (<-b (llvm/BuildStore *base base))

      continue-blk (get-in-plan [:gc :continue-blk])
      _ (<- (assert continue-blk))

      _ (<-b (llvm/BuildBr continue-blk))

      _ (set-block old-block)]
     [(const-size-t type-id) block])))

(comment

                       *base (<-b (llvm/BuildIntToPtr base+size i8* "*base"))
                       _ (<-b (llvm/BuildStore *base base))
  )

(defn make-obj-scan-bodies []
  (gen-plan
   [known-types (get-in-plan [:known-types])
    cur-block (get-block)
    base (get-in-plan [:gc :base])
    *base (<-b (llvm/BuildLoad base "*base"))
    typeid (TYPEID *base)
    results (all (for [[ns-name types] known-types
                       [type-name data] types]
                   (make-obj-scan-body ns-name type-name data)))

    old-block (get-block)
    failed (add-block "failed")
    _ (set-block failed)
    _ (<-b (llvm/BuildRet (const-size-t 42)))
    _ (set-block old-block)

    switch (<-b (llvm/BuildSwitch typeid failed (count results)))
    _ (all (for [[type-id block] results]
           (<- (llvm/AddCase switch type-id block))))]
   nil))

(def obj_scan_t (function-type [i8* i8* i8*] size-t))

(defn make-obj-scan []
  (gen-plan
   [f (add-function "obj_scan" obj_scan_t)
    _ (set-function f)

    entry-blk (add-block "entry")
    _ (set-block entry-blk)

    arg0 (param 0)
    _ (MPS_BEGIN arg0)

    arg1 (param 1)

    base (<-b (llvm/BuildAlloca i8* "base"))
    _ (<-b (llvm/BuildStore arg1 base))

    _ (assoc-in-plan [:gc :base] base)

    loop-entry (add-block "loop-entry")
    *base (<-b (llvm/BuildLoad base "*base"))
    base_i (<-b (llvm/BuildPtrToInt *base size-t "base_i"))
    limit (param 2)
    limit_i (<-b (llvm/BuildPtrToInt limit size-t "limit_i"))

    blt (<-b (llvm/BuildICmp llvm/LLVMIntULT base_i limit_i "blt"))
    continue-scan (add-block "continue-scan")

    _ (assoc-in-plan [:gc :continue-blk] continue-scan)

    finished-blk (add-block "finished")
    _ (<-b (llvm/BuildCondBr blt continue-scan finished-blk))

    _ (set-block continue-scan)

    _ (<-b (llvm/BuildBr loop-entry))
    _ (set-block loop-entry)

    _ (make-obj-scan-bodies)

    _ (set-block finished-blk)

    _ (MPS_SCAN_END)


    _ (<-b (llvm/BuildRet (const-size-t 0)))]
   nil))

(def obj_skip_t (function-type [i8*] i8*))

(defn make-obj-skip []
  (gen-plan
   [f (add-function "obj_scan" obj_scan_t)
    _ (set-function f)

    entry-blk (add-block "entry")
    _ (set-block entry-blk)

    base (param 0)
    base_i (<-b (llvm/BuildPtrToInt base size-t "base_i"))

    type-id (TYPEID base)

    [_ else-blk] (add-block "else-blk"
                        (gen-plan
                         [_ (<-b (llvm/BuildRet base))]
                         nil))

    known-types (get-in-plan [:known-types])
    results (all (for [[ns-name types] known-types
                       [type-name data] types
                       :let [{:keys [fns type-id]} data]]
                   (add-block (str ns-name "." type-name)
                    (gen-plan
                     [size ((::size fns) base)
                      size (ALIGN-VAL size)
                      base+size (<-b (llvm/BuildAdd base_i size "base+size"))
                      _ (<-b (llvm/BuildRet base+size))]
                     (const-size-t type-id)))))

    switch (<-b (llvm/BuildSwitch type-id else-blk (count results)))
    _ (all (for [[type-id block] results]
             (<- (llvm/AddCase switch type-id block))))]
   nil))

(def obj_pad_t (function-type [i8* size-t] void))

(defn make-obj-pad []
  (gen-plan
   [f (add-function "obj_pad" obj_pad_t)

    _ (set-function f)

    entry-blk (add-block "entry")
    _ (set-block entry-blk)


    arg0 (param 0)
    casted (<-b (llvm/BuildBitCast arg0 (llvm/PointerType pad_t 0) "casted"))
    pad-tid (get-in-plan [:known-types "clojure-metal.gc" "pad_t" :type-id])
    _ (<- (assert pad-tid))

    _ (pad_t->tid= casted (const-size-t pad-tid))
    arg1 (param 1)
    _ (pad_t->size= casted arg1)
    _ (<-b (llvm/BuildRetVoid))]
   nil))

(comment
    _ (FIX gep)

    gep (cons_t->head)
    _ (FIX gep)




x  )

(defn do-it2 []
  (->
   (gen-plan
    [_ (add-externals)
     _ def-fwd_t
     _ def-fwd_small_t
     _ def-pad_t
     _ def-cons_t
                                        ; _ (make-obj-scan)
     _ (make-obj-skip)
     _ (make-obj-pad)
     ]
    nil)
   get-state
   second
   :module
   llvm/dump
   llvm/verify
   llvm/optimize
   llvm/dump
   ))

(do-it2)
