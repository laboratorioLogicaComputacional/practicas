module Pruebas
--Muestra ejemplos de la verificacion de deducciones naturales mediante showCheckDedNat.
where
import SintaxisPL
import DeduccionNatural (ReglaDN(..),showCheckDedNat)
--
--
--
--
--todosLosEjemplos :: IO ()
-- muestra todos los ejemplos.
--todosLosEjemplos =
--    do

--    putStrLn "Ejemplo prueba1:"
--    prueba1

--    putStrLn "Ejemplo prueba2:"
--    prueba2

--    putStrLn "Ejemplo prueba3:"
--    prueba3

--    putStrLn "Ejemplo prueba4:"
--    prueba4

--    putStrLn "Ejemplo prueba5:"
--    prueba5

--    putStrLn "Ejemplo prueba6:"
--    prueba6



prueba1 :: IO ()
prueba1 =
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        (°) :: PL->PL->PL
        f°g= Oor f g
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        gamma= [v1⇒v2, v2⇒v3]
        lpasos =[
                (1,(v1⇒v2,     Prem,       [])),
                (2,(v2⇒v3,     Prem,       [])),
                (3,(v1°v2,     Isup,       [(3,0)])),
                (4,(v1,     Isup,       [(3,0),(4,0)])),
                (5,(v2,     Eimp 4 1,       [(3,0),(4,0)])),
                (6,(v3,     Eimp 5 2,       [(3,0),(4,0)])),
                (7,(v1⇒v3,     Iimp 4 6,       [(3,0),(4,6)])),
                (8,(v2,     Isup,       [(3,0),(4,6),(8,0)])),
                (9,(v3,     Eimp 8 2,       [(3,0),(4,6),(8,0)])),
                (10,(v2⇒v3,     Iimp 8 9,       [(3,0),(4,6),(8,9)])),
                (11,(v3,     Edis 3 7 10,  [(3,0),(4,6),(8,9)])),
                (12,((v1°v2)⇒v3,     Iimp 3 11,  [(3,11),(4,6),(8,9)]))
                ]
        phi = (v1°v2)⇒v3
    in showCheckDedNat gamma lpasos phi

prueba2 :: IO ()
prueba2 =
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        (°) :: PL->PL->PL
        f°g= Oor f g
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        gamma= [v1⇒v2, v2⇒v3]
        lpasos =[
                (1,(v1⇒v2,     Prem,       [])),
                (2,(v2⇒v3,     Prem,       [])),
                (3,(v1,     Isup,       [(3,0)])),
                (4,(v2,     Eimp 3 1,   [(3,0)])),
                (5,(v3,     Eimp 4 2,   [(3,0)])),
                (6,(v1⇒v3,     Iimp 3 5,   [(3,5)]))

                ]
        phi = v1⇒v3
    in showCheckDedNat gamma lpasos phi

prueba3 :: IO ()
prueba3 =
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        (°) :: PL->PL->PL
        f°g= Oor f g
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        gamma= [(v1°v2)⇒v3]
        lpasos =[
                (1,((v1°v2)⇒v3,     Prem,       [])),
                (2,(v1,     Isup,       [(2,0)])),
                (3,(v1°v2,     Idis1 2,       [(2,0)])),
                (4,(v3,     Eimp 3 1,       [(2,0)])),
                (5,(v1⇒v3,     Iimp 2 4,       [(2,4)])),
                (6,(v2,     Isup,       [(2,4),(6,0)])),
                (7,(v1°v2,     Idis2 6,  [(2,4),(6,0)])),
                (8,(v3,     Eimp 7 1,   [(2,4),(6,0)])),
                (9,(v2⇒v3,     Iimp 6 8, [(2,4),(6,8)])),
                (10,((v1⇒v3)∧(v2⇒v3),     Icon 5 9, [(2,4),(6,8)]))



                ]
        phi = (v1⇒v3)∧(v2⇒v3)
    in showCheckDedNat gamma lpasos phi

prueba4 :: IO ()
prueba4 =
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        (°) :: PL->PL->PL
        f°g= Oor f g
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        gamma= [v1⇒(v2⇒v3)]
        lpasos =[
                (1,(v1⇒(v2⇒v3),     Prem,       [])),
                (2,(v1∧v2,     Isup,       [(2,0)])),
                (3,(v1,     Econ1 2,       [(2,0)])),
                (4,(v2⇒v3,     Eimp 3 1,       [(2,0)])),
                (5,(v2,     Econ2 2,       [(2,0)])),
                (6,(v3,     Eimp 5 4,       [(2,0)])),
                (7,((v1∧v2)⇒v3,     Iimp 2 6,       [(2,6)]))

                ]
        phi = (v1∧v2)⇒v3
    in showCheckDedNat gamma lpasos phi

--PENDIENTE
prueba5 :: IO ()
prueba5 =
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        (°) :: PL->PL->PL
        f°g= Oor f g
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        gamma= [v1⇒v2]
        lpasos =[
                (1,(v1⇒v2,     Prem,       [])),
                (2,(v1,     Isup,       [(2,0)])),
                (3,(v2,     Eimp 2 1,     [(2,0)])),
                (4,((Oneg v1),  Isup,    [(2,0),(4,0)])),
                (5,(v1 ∧ (Oneg v1),  Icon 2 4, [(2,0),(4,0)])),
                (6,(Bot,     Isup,       [(2,0),(4,0),(6,0)])),
                (7,(v1,     Ebot 6,       [(2,0),(4,6),(6,0)]))

                ]
        phi = (v2⇒v1)
    in showCheckDedNat gamma lpasos phi
