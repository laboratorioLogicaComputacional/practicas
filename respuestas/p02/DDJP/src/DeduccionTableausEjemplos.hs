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
