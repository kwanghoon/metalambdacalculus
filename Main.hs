
--------------------------------------------------------------------------------- 
-- Module      : An Implementation of the Meta Lambda Calculus
-- Copyright   : (c) Kwanghoon Choi, 2015
-- License     : BSD3
--
-- Maintainer  : lazyswamp@gmail.com
-- Stability   : Expermental
-- Portability : Portable
--
-- Provides
--  (1) Beta/Epsilon reductions of the meta lambda calculus
--  (2) A compiler of IMP into the meta lambda calculus
--
-- ToDo
--  (1) Parser for the meta lambda calculus
--  (2) Pretty Printer for the meta lambda calculus
--
-- References.
--  (1) The Meta Lambda Calculus (Kazunori Tobisawa, POPL 2015)
--
--------------------------------------------------------------------------------- 

module Main where

main = putStrLn "Hello Meta Lambda Calculus!!"

type Name  = String  -- A set of names
type Level = Int     -- A set of levels 
type NumberOfBindersToSkip = Int     -- the number of binder to skip

{- 
  Note on the Lv function mapping names into levels
 
  Each variable name in the paper is represented by a pair of the name and 
  a level in this implementation, removing the introduction of the Lv function.

  E.g., v =====> v,1

  Hence,
   In the paper   In the implementation
    - v=w          - v and w have the same name and the same level.
    - v!=w         - v and w have the different names or the different levels.
-}

data Term = 
     -- v:Name, d:NumberOfBindersToSkip, sigma:Sub_Lv(v), level:Level 
     Var Name NumberOfBindersToSkip Subst Level 
     
     -- v:Name, level:Level term:Term
   | Lam Name Level Term
     
   | App Level Term Term  -- l:Level
     
   deriving (Show, Eq)

type Subst = [SingleSubst]

data SingleSubst =
     Push Name Level Term
   | Pop  Name Level
   deriving (Show, Eq)
            
            
var v   = Var v 0 [] 1
app m n = App 1 m n
lam x m = Lam x 1 m

---------------------------------------------------------------------------------
-- Example 3.2
---------------------------------------------------------------------------------

example1 = 
   App 1 
     (Lam "x" 1 (Var "y" 0 [] 1))
     (Var "z" 0 [] 1)
     
example2 =
   Var "M" 0 [Push "x" 1 (Var "N" 1 [] 2),
              Pop  "x" 1,
              Push "y" 1 (Lam "x" 1 (Var "M" 2 [Pop "y" 1, Pop "z" 1] 2))] 2
                
---------------------------------------------------------------------------------

{- Beta Reduction: M ->beta N -}
betaReduce :: Term -> Term
betaReduce term@((App l (Lam v l1 term1) term2)) = 
   if l1==l 
   then star term1 [Push v l1 term2] 
   else term
betaReduce term = term
                                           
{- M*sigma -}
star :: Term -> Subst -> Term
star (Var v d tau l) sigma = 
  if substGeThan sigma l == tau && tau == [] 
  then Var v d sigma l
  else componentOf sigma v l d  `star` substLtThan (compositionOf tau sigma) l
       
star (Lam v l m) sigma = Lam v l (star m (doublePop v l sigma))

star (App l m n) sigma = App l (star m sigma) (star n (substGeThan sigma l))

doublePop :: Name -> Level -> Subst -> Subst
doublePop v l sigma = 
  Push v l (Var v 0 [] l) : compositionOf sigma [Pop v l]

{- tau o sigma  -}
compositionOf :: Subst -> Subst -> Subst
compositionOf [] sigma = sigma
compositionOf (Push v l m : tau) sigma = 
  Push v l (m `star` (substGeThan sigma l)) : compositionOf tau sigma
compositionOf (Pop v l : tau) sigma =   
  Pop v l : (compositionOf tau sigma)

{- sigma<l -}
substLtThan :: Subst -> Level -> Subst
substLtThan sigma l = restrictionOf sigma (<l)

{- sigma>=l -}  
substGeThan :: Subst -> Level -> Subst
substGeThan sigma l = restrictionOf sigma (>=l)

{- sigma ^ S  -}
restrictionOf :: Subst -> (Level -> Bool) -> Subst
restrictionOf [] s = []
restrictionOf (Push v l m : sigma) s = 
  if s l 
  then Push v l m : (restrictionOf sigma s) 
  else restrictionOf sigma s
restrictionOf (Pop v l : sigma) s =        
  if s l
  then Pop v l : (restrictionOf sigma s) 
  else restrictionOf sigma s

{- sigma<v,d>  -}
componentOf :: Subst -> Name -> Level -> NumberOfBindersToSkip -> Term
componentOf [] v l d = Var v d [] l
componentOf (Push w lw m : sigma) v l d =
  if v==w && lw==l && d==0 
  then m 
  else componentOf sigma v l (d - delta v w)
componentOf (Pop w lw : sigma) v l d =        
  componentOf sigma v l (d + delta v w)
       
delta v w = if v == w then 1 else 0


---------------------------------------------------------------------------------
-- Example in 3.4 Equivalence on Terms
---------------------------------------------------------------------------------

example3 = \term -> 
  App 1 
  (Lam "x" 1 term)
  (Var "y" 0 [] 1)

example4 = 
  App 1 
    (Lam "y" 1 (Var "N" 0 [] 2))
    (Var "z" 0 [] 1)

-- 1. Beta-reduce in the inner-most redexes

{- betaReduce example4 -}
example5 = 
  Var "N" 0 [Push "y" 1 (Var "z" 0 [] 1)] 2

example6 = example3 example5

{- betaReduce example6 -}
example7 = 
  Var "N" 0 
  [Push "y" 1 (Var "z" 0 [] 1),
   Push "x" 1 (Var "y" 0 [] 1)] 2



-- 2. Beta-reduce in the outer-most redexes

{- betaReduce (example3 example4) -}
example8 = 
  App 1 
  (Lam "y" 1 
   (Var "N" 0 
    [Push "y" 1 (Var "y" 0 [] 1),
     Push "x" 1 (Var "y" 1 [] 1),
     Pop "y" 1] 2)) 
  (Var "z" 0 [] 1)

{- betaReduce example8 -}
example9 = 
  Var "N" 0 
  [Push "y" 1 (Var "z" 0 [] 1),
   Push "x" 1 (Var "y" 0 [] 1),
   Pop "y" 1,
   Push "y" 1 (Var "z" 0 [] 1)] 2

  
-- The two terms by example7 and example9 are not the same!

---------------------------------------------------------------------------------



{- (A deterministic version of) Epsilon Reduction: M ->epsilon N -}
epsilonReduce :: Term -> Term
epsilonReduce (Var v d sigma l) =
  Var v d (epsilonReduce' sigma) l
epsilonReduce term = term

epsilonReduce' sigma = 
  head $ concat $ [applyEpsilonReduce sigma' | sigma' <- perm sigma]
  where
    head []        = sigma
    head (sigma:_) = sigma
    
perm []                    = [[]]
perm [subst]               = [[subst]]
perm (subst1:subst2:sigma) = 
  if permutable subst1 subst2 
  then map (subst1:) (perm (subst2:sigma))
       ++ map (subst2:) (perm (subst1:sigma))
  else map (subst1:) (perm (subst2:sigma))
    
{- not (v==w && lv==lw)  -}       
permutable (Push v lv m) (Push w lw n) = v/=w && (w<v)  -- || lv/=lw && lw<lv 
permutable (Push v lv m) (Pop w lw)    = v/=w && (w<v)  -- || lv/=lw && lw<lv 
permutable (Pop v lv)    (Pop w lw)    = v/=w && (w<v)  -- || lv/=lw && lw<lv  
permutable (Pop v lv)    (Push w lw n) = v/=w && (w<v)  -- || lv/=lw && lw<lv
    
    
applyEpsilonReduce :: Subst -> [Subst]
applyEpsilonReduce [] = []
applyEpsilonReduce (Pop w lw : Push w' lw' term : sigma) = 
  if w==w' && lw==lw' 
  then [sigma]
  else [Pop w lw : s | s <- applyEpsilonReduce (Push w' lw' term : sigma)]
applyEpsilonReduce (Push w lw (Var w' d [] lw') : sigma) = 
  let theSamePop v l (Pop w lw) = v==w && l==lw
      theSamePop v l _          = False
  in
  if w==w' &&  lw==lw' 
     && length sigma>=d+1 && all (theSamePop w lw) (take (d+1) sigma)
  then [drop 1 sigma]
  else [Push w lw (Var w' d [] lw') : s | s <- applyEpsilonReduce sigma]


---------------------------------------------------------------------------------

{- perm [Push "y" 1 (Var "z" 0 [] 1),
         Push "x" 1 (Var "y" 0 [] 1),
         Pop "y" 1,
         Push "y" 1 (Var "z" 0 [] 1)]  
-}

examplePerm = -- When no ordering on names and leveles are considered
  [
    [Push "y" 1 (Var "z" 0 [] 1),Push "x" 1 (Var "y" 0 [] 1),Pop "y" 1,Push "y" 1 (Var "z" 0 [] 1)],
    [Push "y" 1 (Var "z" 0 [] 1),Pop "y" 1,Push "x" 1 (Var "y" 0 [] 1),Push "y" 1 (Var "z" 0 [] 1)],
    [Push "y" 1 (Var "z" 0 [] 1),Pop "y" 1,Push "y" 1 (Var "z" 0 [] 1),Push "x" 1 (Var "y" 0 [] 1)],
    [Push "x" 1 (Var "y" 0 [] 1),Push "y" 1 (Var "z" 0 [] 1),Pop "y" 1,Push "y" 1 (Var "z" 0 [] 1)]
  ]
  
examplePerm1 = -- when considering the lexicographic order of names or the order of levels
  [
    [Push "y" 1 (Var "z" 0 [] 1),Push "x" 1 (Var "y" 0 [] 1),Pop "y" 1,Push "y" 1 (Var "z" 0 [] 1)],
    [Push "x" 1 (Var "y" 0 [] 1),Push "y" 1 (Var "z" 0 [] 1),Pop "y" 1,Push "y" 1 (Var "z" 0 [] 1)]
  ]

{- [applyEpsilonReduce s | s <- examplePerm] -}
  -- The first, third, and fourth ones are epsilon-Reduced, while the second one
  -- is not reduce.
  --
  -- Actually, the three reductions are actually the same under the permutation 
  -- of substitutions

exampleApplyEpsilonReduction =  
  [
    [[Push "y" 1 (Var "z" 0 [] 1),Push "x" 1 (Var "y" 0 [] 1)]],  
    [],                                                           
    [[Push "y" 1 (Var "z" 0 [] 1),Push "x" 1 (Var "y" 0 [] 1)]],  
    [[Push "x" 1 (Var "y" 0 [] 1),Push "y" 1 (Var "z" 0 [] 1)]]   
  ]

{- [applyEpsilonReduce s | s <- examplePerm1] -}
exampleApplyEpsilonReduction1 =  
  [
    [[Push "y" 1 (Var "z" 0 [] 1),Push "x" 1 (Var "y" 0 [] 1)]],
    [[Push "x" 1 (Var "y" 0 [] 1),Push "y" 1 (Var "z" 0 [] 1)]]
  ]
  
---------------------------------------------------------------------------------

data Expr = 
    NumVar Name
  | Const Int
  | Plus Expr Expr
  | Minus Expr Expr
    deriving Show
             
data PExpr =              
    ProcVar Name
  | Proc [Command]
    deriving Show
    
data Command = 
    Assign Name Expr 
  | ProcAssign Name PExpr 
  | Exec PExpr 
  | If Expr PExpr PExpr 
  | While Expr PExpr 
  | Local PExpr NumVars ProcVars
    deriving Show
    
type NumVars  = [Name]
type ProcVars = [Name]


compileExpr :: Expr -> Term
compileExpr (NumVar v) = var v
compileExpr (Const n) 
  | n<0  = error "Not a natural number"  
  | n==0 = zero 
  | n>0  = app succ_ (compileExpr (Const (n-1)))
compileExpr (Plus expr1 expr2) = 
  app (app plus (compileExpr expr1)) (compileExpr expr2)
compileExpr (Minus expr1 expr2) = 
  app (app minus (compileExpr expr1)) (compileExpr expr2)
  

compilePExpr :: PExpr -> Term
compilePExpr (ProcVar v) = var v
compilePExpr (Proc cs) = App 2 block (compileComms cs)

compileComms :: [Command] -> Term
compileComms cs = foldr f id_ cs 
  where f c mi = App 2 (App 2 comp (compileComm c)) mi

compileComm :: Command -> Term
compileComm (Assign x e) = 
  App 2 (set x) (compileExpr e)
compileComm (ProcAssign z pe) =
  App 2 (set z) (compilePExpr pe)
compileComm (Exec pe) =
  App 2 unblock (compilePExpr pe)
compileComm (If e pe1 pe2) =
  App 2 
  (App 2 
   (App 2 if_ (compileExpr e)) 
   (compilePExpr pe1)) 
  (compilePExpr pe2)
compileComm (While e pe) =
  App 2
  (App 2 while (compileExpr e))
  (compilePExpr pe)
compileComm (Local pe xs zs) =
  App 2 (local xs zs) (compilePExpr pe)
  


--

{- zero = \s z -> z -}
zero = lam "s" (lam "z" (var "z"))
                  
{- scc = \n s z -> s (n s z) -}
succ_ = lam "n"
      (lam "s" 
       (lam "z"
        (app (var "s")
         (app (app (var "n") (var "s")) (var "z") ))))

{- fst = \a b -> a  -}
fst_ = lam "a" (lam "b" (var "a"))

{- snd = \a b -> b -}
snd_ = lam "a" (lam "b" (var "b"))

{- prd = \n -> n (\p c -> c (p snd) (scc (p snd))) (\c -> c zero zero) fst  -}
pred_ = lam "n" (app 
               (app 
                (app 
                 (var "n") 
                 (lam "p" (lam "c"
                           (app (app (var "c") (app (var "p") snd_))
                            (app succ_ (app (var "p") snd_))))))
                (lam "c" (app (app (var "c") zero) zero)))
               fst_)

{- plus = \m n -> n scc m -}
plus = lam "m" (lam "n" (app (app (var "n") succ_) (var "m")))

{- minus = \m n -> n prd m -}
minus = lam "m" (lam "n" (app (app (var "n") pred_) (var "m")))

{- block = \Y x -> x @2 Y  -}
block = Lam "Y" 2 (lam "x" (App 2 (var "x") (Var "Y" 0 [] 2)))

{- unblock = \Z -> Z (\Y -> Y)  -}
unblock = Lam "Z" 2 (app (Var "Z" 0 [] 2) (Lam "Y" 2 (Var "Y" 0 [] 2)))

{- set_v = \E K -> (\v -> K) E -}
set v = Lam "E" 2 (Lam "K" 2 (app (lam v (Var "K" 0 [] 2)) (Var "E" 0 [] 2)))

{- if = \E P Q K -> E (\z -> fst) snd (P @2 K) (Q @2 K) -}
if_ = Lam "E" 2 
      (Lam "P" 2 
       (Lam "Q" 2 
        (Lam "K" 2
         (app 
          (app 
           (app 
            (app (Var "E" 0 [] 2) (lam "z" fst_)) 
            snd_) 
           (App 2 (Var "P" 0 [] 2) (Var "K" 0 [] 2))) 
          (App 2 (Var "Q" 0 [] 2) (Var "K" 0 [] 2))))))

{- while = fix @2 (\W E P -> if @2 E @2 loop @2 id)  -}
while = App 2 fix_
        (Lam "W" 2 
         (Lam "E" 2 
          (Lam "P" 2 
           (App 2 
            (App 2 
             (App 2 
              if_ 
              (Var "E" 0 [] 2)) 
             loop) 
            id_))))

{- fix_ = \F -> (\X -> F @2 (X @2 X)) @2 (\X -> F @2 (X @2 X)) -}
fix_ = Lam "F" 2 (App 2 m m)
  where m = Lam "X" 2 
            (App 2 
             (Var "F" 0 [] 2) 
             (App 2 (Var "X" 0 [] 2) 
              (Var "X" 0 [] 2)))


{- id_ = \K -> K -}
id_ = Lam "K" 2 (Var "K" 0 [] 2)

{- loop = comp @2 P @2 (W @2 E @2 P)  -}
loop = App 2
       (App 2 comp (Var "P" 0 [] 2))
       (App 2
        (App 2
         (Var "W" 0 [] 2)
         (Var "E" 0 [] 2))
        (Var "P" 0 [] 2))
       
{- comp = \P Q K -> P @2 (Q @2 K)  -}
comp = Lam "P" 2 
       (Lam "Q" 2 
        (Lam "K" 2 
         (App 2 
          (Var "P" 0 [] 2) 
          (App 2 (Var "Q" 0 [] 2) (Var "K" 0 [] 2)))))


{- local xs zs = \P K -> (export xs zs) (\K xs zs -> K) P -}
local xs zs = 
  Lam "P" 2 
  (Lam "K" 2 
   (app 
    (app 
     (export xs zs) m)
    (Var "P" 0 [] 2)))
  where m  = Lam "K" 2 (foldr lam m0 (xs ++ zs))
        m0 = Var "K" 0 [] 2

{- export xs zs = \e r -> (e @2 K) (r @2 x1) ... (r @2 zk) -}
export xs zs = lam "e" (lam "r" m)
  where m  = foldl app m0 ms
        ms = [App 2 (var "r") (var x) | x <- xs ++ zs]
        m0 = App 2 (var "e") (Var "K" 0 [] 2)   -- "K" as a free variable

---------------------------------------------------------------------------------

{- Section 4.3 -}
        
-- L = (\p -> (unblock @2 p)) (block @2 (n (unblock @2 p)))
exampleL = 
  app 
  (lam "p" 
   (App 2 unblock (var "p"))) 
  (App 2 
   block 
   (app 
    (var "n") 
    (App 2 unblock (var "p"))))
  
{- To show L => M =>* n M =>* n (n M) ...

   exampleL 
   => exampleL1 
   => exampleL2 
   => exampleL5 
   => exampleL6 
   => exampleL7 
   =  n exampleL8 
   =  n exampleL1 
-}

-- betaReduce exampleL
exampleL1 = 
  App 2 
  (Lam "Z" 2 (App 1 (Var "Z" 0 [Push "p" 1 (App 2 (Lam "Y" 2 (Lam "x" 1 (App 2 (Var "x" 0 [] 1) (Var "Y" 0 [] 2)))) (App 1 (Var "n" 0 [] 1) (App 2 (Lam "Z" 2 (App 1 (Var "Z" 0 [] 2) (Lam "Y" 2 (Var "Y" 0 [] 2)))) (Var "p" 0 [] 1))))] 2) (Lam "Y" 2 (Var "Y" 0 [Push "p" 1 (App 2 (Lam "Y" 2 (Lam "x" 1 (App 2 (Var "x" 0 [] 1) (Var "Y" 0 [] 2)))) (App 1 (Var "n" 0 [] 1) (App 2 (Lam "Z" 2 (App 1 (Var "Z" 0 [] 2) (Lam "Y" 2 (Var "Y" 0 [] 2)))) (Var "p" 0 [] 1))))] 2)))) 
  (Var "p" 0 [] 1)
  
  
{- Rephrased as exampleL1' (since exampleL1 == exampleL1') -}
exampleL1' =  
  App 2 
  (Lam "Z" 2 
   (App 1 
    (Var "Z" 0 subst 2) 
    (Lam "Y" 2 (Var "Y" 0 subst 2)))) 
  (var "p")
  where subst = [Push "p" 1 (App 2 block (App 1 (var "n") (App 2 unblock (Var "p" 0 [] 1))))]
  
  
-- exampleL2 = betaReduce exampleL1  
exampleL2 = exampleFL2 exampleL3
  
  
exampleFL2 = \m ->   
  App 1 m (Lam "Y" 2 (Var "Y" 0 [Push "p" 1 (App 2 (Lam "Y" 2 (Lam "x" 1 (App 2 (Var "x" 0 [] 1) (Var "Y" 0 [] 2)))) (App 1 (Var "n" 0 [] 1) (App 2 (Lam "Z" 2 (App 1 (Var "Z" 0 [] 2) (Lam "Y" 2 (Var "Y" 0 [] 2)))) (Var "p" 0 [] 1))))] 2))
  
  
exampleL3 = App 2 (Lam "Y" 2 (Lam "x" 1 (App 2 (Var "x" 0 [] 1) (Var "Y" 0 [] 2)))) (App 1 (Var "n" 0 [] 1) (App 2 (Lam "Z" 2 (App 1 (Var "Z" 0 [] 2) (Lam "Y" 2 (Var "Y" 0 [] 2)))) (Var "p" 0 [] 1)))  
  

-- exampleL5 = betaReduce exampleL2
-- where exampleL4 is a beta-reduced term of the subterm of exampleL2
exampleL4 = 
  Lam "x" 1 (App 2 (Var "x" 0 [] 1) (App 1 (Var "n" 0 [] 1) (App 2 (Lam "Z" 2 (App 1 (Var "Z" 0 [] 2) (Lam "Y" 2 (Var "Y" 0 [] 2)))) (Var "p" 0 [] 1))))

exampleL5 = exampleFL2 exampleL4

-- exampleL6 = betaReduce exampleL5
exampleL6 = 
  App 2 (Lam "Y" 2 (Var "Y" 0 [Push "p" 1 (App 2 (Lam "Y" 2 (Lam "x" 1 (App 2 (Var "x" 0 [] 1) (Var "Y" 0 [] 2)))) (App 1 (Var "n" 0 [] 1) (App 2 (Lam "Z" 2 (App 1 (Var "Z" 0 [] 2) (Lam "Y" 2 (Var "Y" 0 [] 2)))) (Var "p" 0 [] 1))))] 2)) (App 1 (Var "n" 0 [] 1) (App 2 (Lam "Z" 2 (App 1 (Var "Z" 0 [] 2) (Lam "Y" 2 (Var "Y" 0 [] 2)))) (Var "p" 0 [] 1)))

-- exampleL7 = betaReduce exampleL6
exampleL7 = 
  App 1 (Var "n" 0 [] 1) exampleL8
  
exampleL8 =   
  (App 2 (Lam "Z" 2 (App 1 (Var "Z" 0 [Push "p" 1 (App 2 (Lam "Y" 2 (Lam "x" 1 (App 2 (Var "x" 0 [] 1) (Var "Y" 0 [] 2)))) (App 1 (Var "n" 0 [] 1) (App 2 (Lam "Z" 2 (App 1 (Var "Z" 0 [] 2) (Lam "Y" 2 (Var "Y" 0 [] 2)))) (Var "p" 0 [] 1))))] 2) (Lam "Y" 2 (Var "Y" 0 [Push "p" 1 (App 2 (Lam "Y" 2 (Lam "x" 1 (App 2 (Var "x" 0 [] 1) (Var "Y" 0 [] 2)))) (App 1 (Var "n" 0 [] 1) (App 2 (Lam "Z" 2 (App 1 (Var "Z" 0 [] 2) (Lam "Y" 2 (Var "Y" 0 [] 2)))) (Var "p" 0 [] 1))))] 2)))) (Var "p" 0 [] 1))
  
  
{- exampleL1 == exampleL8 !!! -}


---------------------------------------------------------------------------------

