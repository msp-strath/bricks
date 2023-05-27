module Sketch where

{-
This file is a preliminary exercise for brick construction.

It gives a notion of telescope for which permitted dependency of later field
types on earlier field values is explicitly selective. That is, when extending
a telescope (on the local end), you must explicitly nominate the earlier
fields on which the new field type may depend. Of course, such dependency
selections must be hereditarily closed: if you want to depend on a field, you
must depend on *its* dependencies.
-}


------------------------------------------------------------------------------
-- Library materials
------------------------------------------------------------------------------

data Zero : Set where

record One : Set where constructor <>
record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x

subst : forall {X}{x y : X}(q : x ~ y)(P : X -> Set) -> P x -> P y
subst r~ P p = p

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}


------------------------------------------------------------------------------
-- Thinnings and their composition relation
------------------------------------------------------------------------------

data _<=_ : Nat -> Nat -> Set where
  no : forall {n m} -> n <= m -> n <= su m
  su : forall {n m} -> n <= m -> su n <= su m
  ze : ze <= ze

data [_-_]~_ : forall {l n m} -> l <= n -> n <= m -> l <= m -> Set where
  nr : forall {l n m}{th : l <= n}{ph : n <= m}{ps : l <= m}
      -> [ th - ph ]~ ps
      -> [ th - no ph ]~ no ps
  nl : forall {l n m}{th : l <= n}{ph : n <= m}{ps : l <= m}
      -> [ th - ph ]~ ps
      -> [ no th - su ph ]~ no ps
  su : forall {l n m}{th : l <= n}{ph : n <= m}{ps : l <= m}
      -> [ th - ph ]~ ps
      -> [ su th - su ph ]~ su ps
  ze : [ ze - ze ]~ ze


------------------------------------------------------------------------------
-- Telescopes (length-indexed)
------------------------------------------------------------------------------

data Tel : Nat -> Set1
[_]T : forall {n} -> Tel n -> Set
data Tel where
  [] : Tel ze
  _-,_ : forall {n} -> (Ss : Tel n)(S : [ Ss ]T -> Set) -> Tel (su n)
[ [] ]T = One
[ Ss -, S ]T = [ Ss ]T >< \ s -> S s


------------------------------------------------------------------------------
-- Telescopes with explicit dependency
------------------------------------------------------------------------------

-- We need these dependent telescopes to be length-indexed so we can select
-- from them with thinnings.
data Dep : Nat -> Set1

-- But not all selections are hereditarily closed, so we must specify which
-- selections are ok.
data OK : {n m : Nat} -> n <= m -> Dep m -> Set

-- Given any downward-closed selection, we should be able to extract a valid
-- telescope of exactly those fields.
[_]D : forall {n m}{th : n <= m}{G : Dep m} -> OK th G -> Tel n

-- Moreover, if we refine a valid selection to a smaller valid selection,
-- we should be able to select exactly the fields retained.
sel : forall {l n m}{th : l <= n}{ph : n <= m}{ps : l <= m}
  {G : Dep m}
  (j : OK ps G)(k : OK ph G)(v : [ th - ph ]~ ps)
  -> [ [ k ]D ]T
  -> [ [ j ]D ]T

-- And yes, selection must be closed under composition!
sel~ : forall {l n p m}{th : l <= n}{ph : n <= m}{ps : l <= m}
                     {th' : p <= m }{ph' : l <= p}{ps' : n <= p}
    {G : Dep m}
  (i : OK ps G)(j : OK ph G)(k : OK th' G)
  (u : [ th - ph ]~ ps)(v : [ ps' - th' ]~ ph)(w : [ ph' - th' ]~ ps)
  (ss : [ [ k ]D ]T)
  ->
  sel i k w ss ~ (sel i j u (sel j k v ss))

data Dep where

  -- Kick off with the empty telescope.
  [] : Dep ze

  -- To grow an existing telescope, choose and validate a selection of its
  -- fields, then choose a type depending on only those fields.
  _-[_/_/_] : forall {m}(G : Dep m){n}(th : n <= m)(k : OK th G)
    (S : [ [ k ]D ]T -> Set) -> Dep (su m)

data OK where

  -- Choosing none of no fields is hereditarily closed.
  [] : OK ze []

  -- It's always ok to choose *not* to depend on the *most* local field...
  _-no : forall {m}{G : Dep m}{l}{ps : l <= m}{k : OK ps G}
    {S : [ [ k ]D ]T -> Set}
    {n}{ph : n <= m} ->
    OK ph G -> OK (no ph) (G -[ ps / k / S ])

  -- ...until you find out that you need it. If you want to keep the most
  -- local field, you must check that its dependencies are amongst the
  -- fields you have kept already, i.e. that its dependency selection
  -- factors through yours.
  _-su_/_/_ : forall {m}{G : Dep m}{l}{ps : l <= m}
    {n}{ph : n <= m} ->
    OK ph G ->
    (k : OK ps G)
    (S : [ [ k ]D ]T -> Set)
    {th : l <= n} -> [ th - ph ]~ ps ->
    OK (su ph) (G -[ ps / k / S ])

-- Now, we need to use the validity of the selection to construct the selected
-- telescope. When there's nothing to see or we choose not to look, it's easy.
[ [] ]D = []
[ k -no ]D = [ k ]D
-- But when we keep a field, we must feed its type only the selection of the
-- earlier values that it needs.
[ k -su j / S / v ]D = [ k ]D -, \ ss -> S (sel j k v ss)

-- Selection is easy when you don't...
sel [] [] ze ss = <>
sel (j -no) (k -no) (nr v) ss = sel j k v ss
sel (j -no) (k -su _ / _ / x) (nl v) (ss , _) = sel j k v ss
-- ...but rather more intriguing when you do, because it requires closure
-- under composition to show that the fields a thing needs from the whole
-- are still available amongst the fields you have selected.
sel (j -su i / S / u) (k -su .i / .S / w) (su v) (ss , s) =
  sel j k v ss , subst (sel~ i j k u v w ss) S s

-- Closure of selection under composition is easy when you don't...
-- (nothing to see)
sel~ [] [] [] ze ze ze <> = r~
-- (we never had it)
sel~ (i -no) (j -no) (k -no) (nr u) (nr v) (nr w) ss
  = sel~ i j k u v w ss
-- (the earlier selection threw it away)
sel~ (i -no) (j -no) (k -su _ / _ / x) (nr u) (nl v) (nl w) (ss , s)
  = sel~ i j k u v w ss
-- (the later selection threw it away)
sel~ (i -no) (j -su _ / _ / _) (k -su _ / _ / _) (nl u) (su v) (nl w) (ss , s)
  = sel~ i j k u v w ss
-- ...but an epic game of with-jenga when you do!
-- (the field is retained)
sel~ (i -su h / S / x) (j -su .h / _ / y) (k -su .h / _ / z)
  (su u) (su v) (su w) (ss , s)
  with ss0 <- sel h k z ss
     | q0 <- sel~ h j k y v z ss
     | q1 <- sel~ h i k x w z ss
  with ss1 <- sel i k w ss
     | ss2 <- sel j k v ss
     | q2  <- sel~ i j k u v w ss
  with ss3 <- sel h j y ss2
     | q3  <- sel~ h i j x u y ss2
  with r~ <- q0
     | r~ <- q2
     | r~ <- q1
     | r~ <- q3 -- K!
  = r~

