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
--Implicacion
tEjem3 :: Bool
tEjem3 =
    let 
        v1= Var 1
        v2= Var 2
    in
    checkTableau (UnaRama ([Oimp v1 v2],Sep,[v1]) ImpD (Hoja ([v1,v2],Closed,[v1])))

tEjem4 :: Bool
tEjem4 =
  let
    v1 = Var 1
    v2 = Var 2
    in
    checkTableau (DosRamas ([Oimp v1 v2], Sep,[v1,v2]) ImpI (Hoja ([v1], Closed, [v1,v2])) (Hoja ([v2], Closed, [v1,v2])))
--Conjuncion Derecha
tEjem5 :: Bool
tEjem5 =
  let
    v1 = Var 1
    v2 = Var 2
    in
    checkTableau (DosRamas ([Oand v1 v2], Sep,[v1,v2]) ConD (Hoja ([v1], Closed, [v1,v2])) (Hoja ([v2], Closed, [v1,v2])))
--Disyuncion Derecha
tEjem6 :: Bool
tEjem6 =
  let
    v1 = Var 1
    v2 = Var 2
    in
    checkTableau (UnaRama ([Oor v1 v2],Sep,[v1]) DisD (Hoja ([v1,v2],Closed,[v1])))
--Negacion
tEjem7 :: Bool
tEjem7 =
  let
    v1 = Var 1
    v2 = Var 2
    in
    checkTableau (UnaRama ([Oneg(Oor v1 v2)],Sep,[v1]) NegI (Hoja ([v1,v2],Closed,[v1])))

tEjem8 :: Bool
tEjem8 =
  let
    v1 = Var 1
    v2 = Var 2
    in
    checkTableau (UnaRama ([Oneg(Oor v1 v2)],Sep,[v1]) NegD (Hoja ([v1,v2],Closed,[v1])))
--Doble Implicacion