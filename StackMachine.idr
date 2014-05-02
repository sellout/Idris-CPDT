%default total

||| This is an Idris translation of Chapter 2 of “Certified Programming with
||| Dependent Types” (http://adam.chlipala.net/cpdt/html/StackMachine.html)

-- 2.1.1

data binop : Type where
  Plus : binop
  Times : binop

%elim
data exp : Type where
  Const : Nat -> exp
  Binop : binop -> exp -> exp -> exp

binopDenote : binop -> Nat -> Nat -> Nat
binopDenote Plus = plus
binopDenote Times = mult

expDenote : exp -> Nat
expDenote (Const n) = n
expDenote (Binop b e1 e2) = binopDenote b (expDenote e1) (expDenote e2)

{-
> expDenote (Const 42)
42 : Nat
> expDenote (Binop Plus (Const 2) (Const 2))
4 : Nat
> expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))
28 : Nat
-}

-- 2.1.2

data instr : Type where
  iConst : Nat -> instr
  iBinop : binop -> instr

prog : Type
prog = List instr

stack : Type
stack = List Nat

instrDenote : instr -> stack -> Maybe stack
instrDenote (iConst n) s                = Just (n :: s)
instrDenote (iBinop b) (arg1::arg2::s') = Just (binopDenote b arg1 arg2 :: s')
instrDenote (iBinop b) _                = Nothing

progDenote : prog -> stack -> Maybe stack
progDenote []      s = Just s
progDenote (i::p') s = case instrDenote i s of
  Nothing => Nothing
  Just s' => progDenote p' s'

-- 2.1.3

compile : exp -> prog
compile (Const n) = [iConst n]
compile (Binop b e1 e2) = compile e2 ++ compile e1 ++ [iBinop b]

{-
> compile (Const 42)
[iConst 42] : List instr
> compile (Binop Plus (Const 2) (Const 2))
[iConst 2, iConst 2, iBinop Plus] : List instr
> compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))
[iConst 7, iConst 2, iConst 2, iBinop Plus, iBinop Times] : List instr
> progDenote (compile (Const 42)) []
Just [42] : Maybe (List Nat)
> progDenote (compile (Binop Plus (Const 2) (Const 2))) []
Just [4] : Maybe (List Nat)
> progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))) []
Just [28] : Maybe (List Nat)
-}

-- 2.1.4

compileCorrect : (e : exp) -> progDenote (compile e) [] = Just (expDenote e `Prelude.List.(::)` [])
compileCorrect = ?compileCorrectTheorem

compileCorrect' : (e : exp) -> (p : prog) -> (s : stack) ->
                  progDenote (compile e ++ p) s = progDenote p (expDenote e :: s)
compileCorrect' = proof
  intro
  induction e
  intros
  compute
  refine refl
  intros
  compute
  rewrite appendAssociative (compile e__2) (compile e__0 ++ [iBinop b__0]) p
  rewrite sym (ihe__2 ((compile e__0 ++ [iBinop b__0]) ++ p) s)
  rewrite appendAssociative (compile e__0) [iBinop b__0] p
  rewrite sym (ihe__0 (iBinop b__0 :: p) (expDenote e__2 :: s))
  refine refl
--   abandon
--   intro
--   induction e
--   crush

compileCorrectTheorem = proof
  intros
  rewrite appendNilRightNeutral (compile e)
  rewrite compileCorrect' e [] []
  refine refl

-- 2.2.1

data type : Type where
  nat : type
  bool : type

data tbinop : type -> type -> type -> Type where
  TPlus : tbinop nat nat nat
  TTimes : tbinop nat nat nat
  TEq : (t : type) -> tbinop t t bool
  TLt : tbinop nat nat bool

data texp : type -> Type where
  TNConst : Nat -> texp nat
  TBConst : Bool -> texp bool
  TBinop : tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t

typeDenote : type -> Type
typeDenote nat = Nat
typeDenote bool = Bool

tbinopDenote : tbinop arg1 arg2 res ->
               typeDenote arg1 -> typeDenote arg2 -> typeDenote res
tbinopDenote TPlus = plus
tbinopDenote TTimes = mult
tbinopDenote {arg1=nat} {arg2=nat} (TEq nat) = (==)
tbinopDenote {arg1=bool} {arg2=bool} (TEq bool) = (==)
tbinopDenote TLt = (<)

texpDenote : texp t -> typeDenote t
texpDenote (TNConst n) = n
texpDenote (TBConst b) = b
texpDenote (TBinop b e1 e2) = tbinopDenote b (texpDenote e1) (texpDenote e2)

{-
> texpDenote (TNConst 42)
42 : Nat
> texpDenote (TBConst True)
True : Bool
> texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7))
28 : Nat
> texpDenote (TBinop (TEq nat) (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7))
False : Bool
> texpDenote (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7))
True : Bool
-}

-- 2.2.2

tstack : Type
tstack = List type

data tinstr : tstack -> tstack -> Type where
  TiNConst : (s : tstack) -> Nat -> tinstr s (nat :: s)
  TiBConst : (s : tstack) -> Bool -> tinstr s (bool :: s)
  TiBinop : (s : tstack) -> tbinop arg1 arg2 res -> tinstr (arg1 :: arg2 :: s) (res :: s)

data tprog : tstack -> tstack -> Type where
  TNil : (s : tstack) -> tprog s s
  TCons : tinstr s1 s2 -> tprog s2 s3 -> tprog s1 s3

vstack : tstack -> Type
vstack [] = ()
vstack (t::ts) = (typeDenote t, vstack ts)

tinstrDenote : tinstr ts ts' -> vstack ts -> vstack ts'
tinstrDenote (TiNConst _ n) s = (n, s)
tinstrDenote (TiBConst _ b) s = (b, s)
tinstrDenote (TiBinop _ b) s =
  let (arg1, (arg2, s')) = s
  in (tbinopDenote b arg1 arg2, s')

tprogDenote : tprog ts ts' -> vstack ts -> vstack ts'
tprogDenote (TNil _) s = s
tprogDenote (TCons i p) s = tprogDenote p (tinstrDenote i s)

-- 2.2.3

tconcat : tprog ts ts' -> tprog ts' ts'' -> tprog ts ts''
tconcat (TNil _) p = p
tconcat (TCons i p1) p = TCons i (tconcat p1 p)

tcompile : texp t -> (ts : tstack) -> tprog ts (t :: ts)
tcompile (TNConst n) ts = TCons (TiNConst ts n) (TNil (nat :: ts))
tcompile (TBConst b) ts = TCons (TiBConst ts b) (TNil (bool :: ts))
tcompile (TBinop {t2=arg2} {t=res} b e1 e2) ts =
  tconcat (tcompile e2 ts)
          (tconcat (tcompile e1 (arg2 :: ts))
                   (TCons (TiBinop ts b) (TNil (res :: ts))))

{-
> tprogDenote (tcompile (TNConst 42) []) ()
(42, ()) : (Nat, ())
> tprogDenote (tcompile (TBConst True) []) ()
(True, ()) : (Bool, ())
> tprogDenote (tcompile (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)) []) ()
(28, ()) : (Nat, ())
> tprogDenote (tcompile (TBinop (TEq nat) (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)) []) ()
(False, ()) : (Bool, ())
> tprogDenote (tcompile (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)) []) ()
(True, ()) : (Bool, ())
-}

-- 2.2.4

tcompileCorrect : (e : texp t) ->
                  tprogDenote (tcompile e []) () = (texpDenote e, ())
tcompileCorrect = ?tcompileCorrectTheorem

tcompileCorrect' : (e : texp t) -> (ts : tstack) -> (s: vstack ts) ->
                   tprogDenote (tcompile e ts) s = (texpDenote e, s)
tcompileCorrect' = ?tcompileCorrect'Lemma

tconcatCorrect : (p : tprog ts ts') -> (p' : tprog ts' ts'') ->
                 (s : vstack ts) ->
                 tprogDenote (tconcat p p') s = tprogDenote p' (tprogDenote p s)
tconcatCorrect = ?tconcatCorrectLemma
