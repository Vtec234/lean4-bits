/-! https://www.cs.tufts.edu/~nr/cs257/archive/koen-claessen/finger-trees.pdf -/

/-! Idea: normal list. -/
namespace Finger₀

inductive Seq α where
  | nil : Seq α
  | cons : α → Seq α → Seq α
  deriving Inhabited

variable [Inhabited α]

def Seq.head : Seq α → α
  | cons a as => a
  | nil       => panic! "no last"

def Seq.last : Seq α → α
  | cons a nil => a
  | cons a as  => last as -- linear time :(
  | nil        => panic! "no last"

end Finger₀

/-! Idea: constant-time head/last via a symmetric representation. -/
namespace Finger₁

inductive Seq α where
  | nil : Seq α
  | unit : α → Seq α
  | more : α → Seq α → α → Seq α
  deriving Inhabited

variable [Inhabited α]

def Seq.head : Seq α → α
  | unit h    => h
  | more h .. => h
  | nil       => panic! "no head"

def Seq.last : Seq α → α
  | unit l     => l
  | more _ _ l => l
  | nil        => panic! "no last"

def Seq.cons (h : α) : Seq α → Seq α
  | unit l      => more h nil l
  | more a as l => more h (cons a as) l -- now cons is linear
  | nil         => unit h

def Seq.snoc : Seq α → α → Seq α
  | unit h,      l => more h nil l
  | more h as a, l => more h (snoc as a) l
  | nil,         l => unit l

def Seq.tail : Seq α → Seq α
  | unit _      => nil
  | more _ as l => more as.head as.tail l
  | nil         => panic! "no tail"

end Finger₁

/-! Idea: logarithmic complexity by recursively doubling the amount of values per node. -/
namespace Finger₂

inductive Seq : Type u → Type (u + 1) where
  | nil : Seq α
  | unit : α → Seq α
  | more : α → Seq (α × α) → α → Seq α

instance : Inhabited (Seq α) := ⟨Seq.nil⟩

def Seq.cons (h : α) : Seq α → Seq α
  | nil         => unit h
  | unit l      => more h nil l
  | more a as l => more h sorry l -- now we can't represent sequences of odd length

end Finger₂

/-! Idea: represent odd lengths with one/two elements in head/last positions. -/
namespace Finger₃

inductive Some α where
  | one : α → Some α
  | two : α → α → Some α

inductive Seq : Type u → Type (u + 1) where
  | nil : Seq α
  | unit : α → Seq α
  | more : Some α → Seq (α × α) → Some α → Seq α

instance : Inhabited (Seq α) := ⟨Seq.nil⟩

variable [Inhabited α]

open Some

def Seq.head : Seq α → α
  | unit h            => h
  | more (one h) ..   => h
  | more (two h _) .. => h
  | nil               => panic! "no head"

def Seq.last : Seq α → α
  | unit l             => l
  | more _ _ (one l)   => l
  | more _ _ (two _ l) => l
  | nil                => panic! "no last"

def Seq.cons {α : Type u} (h : α) : Seq α → Seq α
  | nil                  => unit h
  | unit l               => more (one h) nil (one l)
  | more (one a) as l    => more (two h a) as l
  | more (two a a') as l => more (one h) (cons (a, a') as) l

partial def Seq.tail {α : Type u} [Inhabited α] : Seq α → Seq α
  | unit _              => nil
  | more (one _) as l   => moreSnoc as l
  | more (two _ h) as l => more (one h) as l
  | nil                 => panic! "no tail"
where
  moreSnoc : Seq (α × α) → Some α → Seq α
    | nil, (one a)   => unit a
    | nil, (two h l) => more (one h) nil (one l)
    | as,  ls        =>
      let (h, a) := as.head
      more (two h a) as.tail ls

-- now we can't implement append sub-linearly because we'd need to destruct
-- all pairs in `more _ as _` when odd-length sequences appear in certain places

end Finger₃

/-! Idea: also allow the log-recursion base to be odd or even. -/
namespace Finger₄

inductive Some α where
  | one (a : α)
  | two (a b : α)
  deriving Inhabited

inductive Tuple α where
  | pair (a b : α)
  | triple (a b c : α)
  deriving Inhabited

inductive Seq : Type u → Type (u + 1) where
  | nil : Seq α
  | unit : α → Seq α
  | more : Some α → Seq (Tuple α) → Some α → Seq α

instance : Inhabited (Seq α) := ⟨Seq.nil⟩

variable [Inhabited α]

open Some Tuple

def Seq.head : Seq α → α
  | unit h            => h
  | more (one h) ..   => h
  | more (two h _) .. => h
  | nil               => panic! "no head"

def Seq.last : Seq α → α
  | unit l             => l
  | more _ _ (one l)   => l
  | more _ _ (two _ l) => l
  | nil                => panic! "no last"

def Seq.cons {α : Type u} (h : α) : Seq α → Seq α
  | nil                  => unit h
  | unit l               => more (one h) nil (one l)
  | more (one a) as l    => more (two h a) as l
  | more (two a a') as l => more (one h) (cons (pair a a') as) l

def Seq.snoc {α : Type u} (s : Seq α) (l : α) : Seq α :=
  match s with
  | nil                   => unit l
  | unit h                => more (one h) nil (one l)
  | more hs as (one a)    => more hs as (two a l)
  | more hs as (two a' a) => more hs (snoc as (pair a' a)) (one l)

partial def Seq.tail {α : Type u} [Inhabited α] : Seq α → Seq α
  | unit _              => nil
  | more (one _) as l   => moreSnoc as l
  | more (two _ h) as l => more (one h) as l
  | nil                 => panic! "no tail"
where
  moreSnoc : Seq (Tuple α) → Some α → Seq α
    | nil, (one a)   => unit a
    | nil, (two h l) => more (one h) nil (one l)
    | as,  ls        => match as.head with
      | pair h a     => more (two h a) as.tail ls
      | triple h a b => more (one h) (map1 chop as) ls
  map1 {α : Type u} (f : α → α) : Seq α → Seq α
    | nil                  => nil
    | unit h               => unit (f h)
    | more (one h) as ls   => more (one $ f h) as ls
    | more (two h a) as ls => more (two (f h) a) as ls
  chop : Tuple α → Tuple α
    | triple a b c => pair b c
    | pair a b => unreachable!

def Some.toList : Some α → List α
  | one a => [a]
  | two a b => [a, b]

private def toTuples : List α → List (Tuple α)
  | [] => []
  | [a, b] => [pair a b]
  | [a, b, c] => [triple a b c]
  | [a, b, c, d] => [pair a b, pair c d]
  | [a, b, c, d, e] => [triple a b c, pair d e]
  | [a, b, c, d, e, f] => [triple a b c, triple d e f]
  | _ => unreachable!

private def Seq.glue {α : Type u} : Seq α → List α → Seq α → Seq α
  | nil,             as, s₂              => as.foldr Seq.cons s₂
  | s₁,              as, nil             => as.foldl Seq.snoc s₁
  | unit h,          as, s₂              => (h :: as).foldr Seq.cons s₂
  | s₁,              as, unit l          => (as ++ [l]).foldl Seq.snoc s₁
  | more hs₁ s₁ ls₁, as, more hs₂ s₂ ls₂ =>
    more hs₁ (glue s₁ (toTuples (ls₁.toList ++ as ++ hs₂.toList)) s₂) ls₂

def append : Seq α → Seq α → Seq α
  | as, bs => Seq.glue as [] bs

end Finger₄

/-! Idea: add a *third* possible head/last length so that there are cases
in which neither cons nor tail needs to recurse, resulting in amortized
constant-time complexity. -/
namespace Finger₅

inductive Some α where
  | one (a : α)
  | two (a b : α)
  | three (a b c : α)
  deriving Inhabited

inductive Tuple α where
  | pair (a b : α)
  | triple (a b c : α)
  deriving Inhabited

inductive Seq : Type u → Type (u + 1) where
  | nil : Seq α
  | unit : α → Seq α
  | more : Some α → Seq (Tuple α) → Some α → Seq α

instance : Inhabited (Seq α) := ⟨Seq.nil⟩

variable [Inhabited α]

open Some Tuple

def Seq.head : Seq α → α
  | unit h               => h
  | more (one h) ..      => h
  | more (two h ..) ..   => h
  | more (three h ..) .. => h
  | nil                  => panic! "no head"

def Seq.last : Seq α → α
  | unit l                 => l
  | more _ _ (one l)       => l
  | more _ _ (two _ l)     => l
  | more _ _ (three _ _ l) => l
  | nil                    => panic! "no last"

def Seq.cons {α : Type u} (h : α) : Seq α → Seq α
  | nil                     => unit h
  | unit l                  => more (one h) nil (one l)
  | more (one a) as l       => more (two h a) as l
  | more (two a b) as l     => more (three h a b) as l
  | more (three a b c) as l => more (two h a) (cons (pair b c) as) l

def Seq.snoc {α : Type u} (s : Seq α) (l : α) : Seq α :=
  match s with
  | nil                      => unit l
  | unit h                   => more (one h) nil (one l)
  | more hs as (one a)       => more hs as (two a l)
  | more hs as (two a b)     => more hs as (three a b l)
  | more hs as (three a b c) => more hs (snoc as (pair a b)) (two c l)

partial def Seq.tail {α : Type u} [Inhabited α] : Seq α → Seq α
  | unit _                  => nil
  | more (one _) as l       => moreSnoc as l
  | more (two _ h) as l     => more (one h) as l
  | more (three _ h a) as l => more (two h a) as l
  | nil                     => panic! "no tail"
where
  moreSnoc : Seq (Tuple α) → Some α → Seq α
    | nil, (one a)       => unit a
    | nil, (two h l)     => more (one h) nil (one l)
    | nil, (three h a l) => more (one h) nil (two a l)
    | as,  ls        => match as.head with
      | pair h a     => more (two h a) as.tail ls
      | triple h a b => more (one h) (map1 chop as) ls
  map1 {α : Type u} (f : α → α) : Seq α → Seq α
    | nil                      => nil
    | unit h                   => unit (f h)
    | more (one h) as ls       => more (one $ f h) as ls
    | more (two h a) as ls     => more (two (f h) a) as ls
    | more (three h a b) as ls => more (three (f h) a b) as ls
  chop : Tuple α → Tuple α
    | triple a b c => pair b c
    | pair a b => unreachable!

def Some.toList : Some α → List α
  | one a => [a]
  | two a b => [a, b]
  | three a b c => [a, b, c]

-- TODO(WN): unrolled but unclear if needed
-- TODO(WN): subtype proofs of in.length ∈ [2,9] and out.length ∈ [1,3]
private def toTuples : List α → List (Tuple α)
  | [] => []
  | [a, b] => [pair a b]
  | [a, b, c] => [triple a b c]
  | [a, b, c, d] => [pair a b, pair c d]
  | [a, b, c, d, e] => [triple a b c, pair d e]
  | [a, b, c, d, e, f] => [triple a b c, triple d e f]
  | [a, b, c, d, e, f, g] => [triple a b c, pair d e, pair f g]
  | [a, b, c, d, e, f, g, h] => [triple a b c, triple d e f, pair g h]
  | [a, b, c, d, e, f, g, h, i] => [triple a b c, triple d e f, triple g h i]
  | _ => unreachable!

private def Seq.glue {α : Type u} : Seq α → List α → Seq α → Seq α
  | nil,             as, s₂              => as.foldr Seq.cons s₂
  | s₁,              as, nil             => as.foldl Seq.snoc s₁
  | unit h,          as, s₂              => (h :: as).foldr Seq.cons s₂
  | s₁,              as, unit l          => (as ++ [l]).foldl Seq.snoc s₁
  | more hs₁ s₁ ls₁, as, more hs₂ s₂ ls₂ =>
    more hs₁ (glue s₁ (toTuples (ls₁.toList ++ as ++ hs₂.toList)) s₂) ls₂

instance : Append (Seq α) :=
  ⟨fun as bs => Seq.glue as [] bs⟩

end Finger₅
