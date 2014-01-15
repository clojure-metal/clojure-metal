(ns clojure-metal.state-monad
  (:require [clojure-metal.llvmc :as llvm]))

(defmacro gen-plan
  "Allows a user to define a state monad binding plan.

  (gen-plan
    [_ (assoc-in-plan [:foo :bar] 42)
     val (get-in-plan [:foo :bar])]
    val)"
  [binds id-expr]
  (let [binds (partition 2 binds)
        psym (gensym "plan_")
        forms (reduce
               (fn [acc [id expr]]
                 (concat acc `[[~id ~psym] (~expr ~psym)]))
               []
               binds)]
    `(fn [~psym]
       (let [~@forms]
         [~id-expr ~psym]))))

(defn get-plan
  "Returns the final [id state] from a plan. "
  [f]
  (f {}))

(defn push-binding
  "Sets the binding 'key' to value. This operation can be undone via pop-bindings.
   Bindings are stored in the state hashmap."
  [key value]
  (fn [plan]
    [nil (update-in plan [:bindings key] conj value)]))

(defn push-alter-binding
  "Pushes the result of (apply f old-value args) as current value of binding key"
  [key f & args]
  (fn [plan]
    [nil (update-in plan [:bindings key]
                  #(conj % (apply f (first %) args)))]))

(defn get-binding
  "Gets the value of the current binding for key"
  [key]
  (fn [plan]
    [(first (get-in plan [:bindings key])) plan]))

(defn pop-binding
  "Removes the most recent binding for key"
  [key]
  (fn [plan]
    [(first (get-in plan [:bindings key]))
     (update-in plan [:bindings key] pop)]))

(defn no-op
  "This function can be used inside a gen-plan when no operation is to be performed"
  []
  (fn [plan]
    [nil plan]))

(defn all
  "Assumes that itms is a list of state monad function results, threads the state map
  through all of them. Returns a vector of all the results."
  [itms]
  (fn [plan]
    (reduce
     (fn [[ids plan] f]
       (let [[id plan] (f plan)]
         [(conj ids id) plan]))
     [[] plan]
     itms)))

(defn assoc-in-plan
  "Same as assoc-in, but for state hash map"
  [path val]
  (fn [plan]
    [val (assoc-in plan path val)]))

(defn update-in-plan
  "Same as update-in, but for a state hash map"
  [path f & args]
  (fn [plan]
    [nil (apply update-in plan path f args)]))

(defn get-in-plan
  "Same as get-in, but for a state hash map"
  [path]
  (fn [plan]
    [(get-in plan path) plan]))

(defn set-block [blk]
  (fn [state]
    {:pre [(:builder state) blk]}
    (llvm/PositionBuilderAtEnd (:builder state) blk)
    [nil (assoc state :block blk)]))

(def get-block (partial get-in-plan [:block]))



(defmacro <- [expr]
  "Allows a normal clojure expression to be used in a gen-plan"
  `(fn [state#]
     [~expr state#]))

(defmacro <-b [[first & rest]]
  "Same as <- but assumes that the first arg to the expression will need to be
   replaced with the :builder from the state map"
  `(fn [state#]
     {:pre [(:builder state#)]}
     [(~first (:builder state#) ~@rest) state#]))

(defn add-block [nm]
  (gen-plan
   [f (get-in-plan [:fn])
    blk (<- (llvm/AppendBasicBlock f (llvm/gen-name nm)))]
   blk))




#_(defn print-plan []
  (fn [plan]
    (pprint plan)
    [nil plan]))
