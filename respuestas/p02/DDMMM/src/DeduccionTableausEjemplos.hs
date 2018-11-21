module DeduccionTableausEjemplos
where
import SintaxisPL
import DeduccionTableaus


-- Ejemplos de Tableaus para verificar las reglas ya hechas

tEjem1 :: Bool
tEjem1 = -- ([v1 ∧ v2],Sep,[v1]) --ConI--> ([v1,v2],Closed,[v1])
    let 
        v1= Var 1
        v2= Var 2
    in
    checkTableau (UnaRama ([Oand v1 v2],Sep,[v1]) ConI (Hoja ([v1,v2],Closed,[v1])))

tEjem2 :: Bool
tEjem2 =
  let
    v1 = Var 1
    v2 = Var 2
    in
    checkTableau (DosRamas ([Oor v1 v2], Sep,[v1,v2]) DisI (Hoja ([v1], Closed, [v1,v2])) (Hoja ([v2], Closed, [v1,v2])))
---
tEjem3 :: Bool
tEjem3 = --([v1] ∧ [v2 v v3], Sep, [v1 ∧ v2] v [v3])
       let
         v1 = Var 1
     v2 = Var 2
     v3 = Var 3
     in
     checkTableau (DosRamas([Oor[v1] [Oand v2 v3]], Sep, [Oor[Oand v1 v2] [v3]]) DisI (Hoja))--Falta!!
tEjem4 :: Bool
tEjem4 = -- ([v1 ∧ v2] v v3, Sep, [v1] ∧ [v2 v v3])
      let
    v1 = Var 1
    v2 = Var 2
    v3 = Var 3
    in
    checkTableau(DosRamas([Oor[Oand v1 v2] [v3]], Sep,[Oand [v1] [Oor v2 v3]]) DisI(Hoja ([Oand v1 v2], Sep, [Oand [v1] [Oor v2 v3])) (DosRamas ([v3], Sep, [Oand [v1] [Oor v2 v3])))ConD(Hoja([v3], Sep, [v1]))) Hoja([v3], Sep, [Oor v2 v3])))))
       
tFig8_2a :: Tableau
tFig8_2a = --([¬p ∧ ¬q, sep, ¬(p ∧ q)])
    let
      p = Var 1
      q = Var 2
      in
      checkTablueau(UnaRama ([Oand (Oneg p) (Oneg q) ], Sep, [Oneg (Oand p  q)]) ConI (UnaRama ([(Oneg p),(Oneg q)],Sep,[Oneg (Oand p q)]))
                    NegD (UnaRama ([(Oneg q, Oand p q)],Sep,[p])) DisI(Hoja ([Oneg q, p], Closed, [p] )))

tFig8_2b :: Tableau
tFig8_2b = 
    let
      p = Var 1
      q = Var 2
      in
      checkTableau(UnaRama ([Oneg (Oand p q)],Sep,[Oand (Oneg p) (Oneg q)]) NegI (DosRamas ([],Sep,[(Oand p q),(Oand (Oneg p) (Oneg q))]))
                   ConD (Hoja ([],Open, [p, Oand (Oneg p) (Oneg q)]) (DosRamas ([],Sep,[q, Oand (Oneg p) (Oneg q)]))) 
                   ConD (UnaRama ([],Sep,[q, Oneg p]) (Hoja ([],Open,[q, Oneg q])) NegD (Hoja ([],Open,[p,q] ))))

