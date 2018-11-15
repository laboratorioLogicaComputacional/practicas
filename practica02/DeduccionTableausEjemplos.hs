module DeduccionTableausEjemplos
where
import SintaxisPL
import DeduccionTableaus3 



--
--
--
--Tableaus: -----------------------------------------------------------------------------
-- 
-- 1. Representar con una variable de tipo Tableau los dos tableaus de 
-- la figura 8.1 (p.8-6) de vanBenthem-vanEijck. Logic in Action, Capítulo 8.
-- tFig8_1a :: Tableau
-- tFig8_1a = ...
-- tFig8_1b :: Tableau
-- tFig8_1b = ...
--
-- 2. Representar con una variable de tipo Tableau los dos tableaus de 
-- la figura 8.2 (p.8-7) de vanBenthem-vanEijck. Logic in Action, Capítulo 8.
-- tFig8_2a :: Tableau
-- tFig8_2a = ...
-- tFig8_2b :: Tableau
-- tFig8_2b = ...
--

tFig8_1a :: Tableau
tFig8_1a =
  let
    v1= Var 1
    v2= Var 2
    v3= Var 3
    (∧) :: PL->PL->PL
    f∧g= Oand f g
    (∨) :: PL->PL->PL
    f∨g= Oor f g
  in
    (UnaRama ([v1∧(v2∨v3)],Sep,[(v1∧v2)∨v3]) (ConI,v1∧(v2∨v3))
    (UnaRama ([v1,v2∨v3],Sep,[(v1∧v2)∨v3]) (DisD,(v1∧v2)∨v3)
    (DosRamas ([v1,v2∨v3],Sep,[(v1∧v2),v3]) (DisI,v2∨v3) -- Primera doble Rama
    (DosRamas ([v1,v2],Sep,[(v1∧v2),v3]) (ConD, v1∧v2)
    (Hoja ([v1,v2],Closed,[v1,v3]))
    (Hoja ([v1,v2],Closed,[v2,v3])))
    (Hoja ([v1,v3],Closed,[v1∧v2,v3])))))

tFig8_1a_dem :: Bool
tFig8_1a_dem =
  let v1= Var 1
      v2= Var 2
      v3= Var 3
      gamma= [(v1∧(v2∨v3))]
      phi= ((v1∧v2)∨v3)
      (∧) :: PL->PL->PL
      f∧g= Oand f g
      (∨) :: PL->PL->PL
      f∨g= Oor f g
      (⇒) :: PL->PL->PL
      f⇒g= Oimp f g
   in
      impLogicaConTableaus gamma phi tFig8_1a
