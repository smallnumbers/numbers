(set-option :produce-proofs true)
(declare-const size Int)
(declare-const x000 Int)
(assert (< x000 2))
(assert (>= x000 0))
(declare-const x001 Int)
(assert (< x001 2))
(assert (>= x001 0))
(declare-const x002 Int)
(assert (< x002 2))
(assert (>= x002 0))
(declare-const x003 Int)
(assert (< x003 2))
(assert (>= x003 0))
(declare-const x004 Int)
(assert (< x004 2))
(assert (>= x004 0))
(declare-const x005 Int)
(assert (< x005 2))
(assert (>= x005 0))
(declare-const x006 Int)
(assert (< x006 2))
(assert (>= x006 0))
(declare-const x007 Int)
(assert (< x007 2))
(assert (>= x007 0))
(declare-const x008 Int)
(assert (< x008 2))
(assert (>= x008 0))
(declare-const x009 Int)
(assert (< x009 2))
(assert (>= x009 0))
(assert (= size (+ x000 x001 x002 x003 x004 x005 x006 x007 x008 x009)))
(assert (> 4 (+ x000 x001 x002 x003)))
(assert (> 4 (+ x000 x002 x004 x006)))
(assert (> 4 (+ x000 x003 x006 x009)))
(assert (> 4 (+ x001 x002 x003 x004)))
(assert (> 4 (+ x001 x003 x005 x007)))
(assert (> 4 (+ x002 x003 x004 x005)))
(assert (> 4 (+ x002 x004 x006 x008)))
(assert (> 4 (+ x003 x004 x005 x006)))
(assert (> 4 (+ x003 x005 x007 x009)))
(assert (> 4 (+ x004 x005 x006 x007)))
(assert (> 4 (+ x005 x006 x007 x008)))
(assert (> 4 (+ x006 x007 x008 x009)))
(assert (>= size 9))
(check-sat)
(get-proof)
