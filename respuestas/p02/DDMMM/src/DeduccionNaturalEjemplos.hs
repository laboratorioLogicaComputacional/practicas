module DeduccionNaturalEjemplos 
--Muestra ejemplos de la verificacion de deducciones naturales mediante showCheckDedNat.
where
import SintaxisPL
import DeduccionNatural (ReglaDN(..),showCheckDedNat)  
--
--
--
--
todosLosEjemplos :: IO ()
-- muestra todos los ejemplos.
todosLosEjemplos =
    do
    putStrLn ""
    putStrLn "Ejemplo thompsonP10:"
    thompsonP10
    --
    putStrLn "Ejemplo thompsonP12a:"
    thompsonP12a
    --
    putStrLn "Ejemplo thompsonP12b:"
    thompsonP12b
    --
    putStrLn "Ejemplo thompsonP12c1:"
    thompsonP12c1
    --
    putStrLn "Ejemplo huthRyanP20:"
    huthRyanP20
    --
    putStrLn "Ejemplo huthRyanP8Ej6:"
    huthRyanP8Ej6
    --
    putStrLn "Ejemplo thompsonP10:"
    thompsonP10
    --
    putStrLn "Ejemplo thompsonP12c2:"
    thompsonP12c2
    --
    
--
thompsonP10 :: IO ()
thompsonP10 = -- |- ((v1&v2)&v3) -> (v1&(v2&v3))
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        gamma= []
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos= [   (1,((v1∧v2)∧v3,             Isup,       [(1,0)])), 
                (2,((v1∧v2),                    Econ1 1,    [(1,0)])), 
                (3,(v1,                         Econ1 2,    [(1,0)])), 
                (4,(v2,                         Econ2 2,    [(1,0)])), 
                (5,(v3,                         Econ2 1,    [(1,0)])), 
                (6,(v2∧v3,                      Icon 4 5,   [(1,0)])), 
                (7,(v1∧(v2∧v3),                 Icon 3 6,   [(1,0)])), 
                (8,(((v1∧v2)∧v3)⇒(v1∧(v2∧v3)),  Iimp 1 7,   [(1,7)]))
                ]
        phi= ((v1∧v2)∧v3)⇒(v1∧(v2∧v3))
    in showCheckDedNat gamma lpasos phi 
--
thompsonP12a :: IO ()
thompsonP12a = -- |- ((v1 ∧ v2) ⇒ v3) ⇒ (v1 ⇒ (v2 ⇒ v3))
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        gamma= []
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos= [   (1,((v1∧v2)⇒v3,                 Isup,       [(1,0)])), 
                    (2,(v1,                         Isup,       [(1,0),(2,0)])), 
                    (3,(v2,                         Isup,       [(1,0),(2,0),(3,0)])), 
                    (4,(v1∧v2,                      Icon 2 3,   [(1,0),(2,0),(3,0)])), 
                    (5,((v1∧v2)⇒v3,                 Copy 1,     [(1,0),(2,0),(3,0)])), 
                    (6,(v3,                         Eimp 4 5,   [(1,0),(2,0),(3,0)])), 
                    (7,(v2 ⇒ v3,                    Iimp 3 6,   [(1,0),(2,0),(3,6)])), 
                    (8,(v1 ⇒(v2 ⇒ v3),              Iimp 2 7,   [(1,0),(2,7),(3,6)])),
                    (9,(((v1∧v2)⇒v3)⇒(v1⇒(v2⇒v3)),  Iimp 1 8,   [(1,8),(2,7),(3,6)])) 
                    ]
        phi= ((v1∧v2)⇒v3)⇒(v1⇒(v2⇒v3))
    in showCheckDedNat gamma lpasos phi
--
thompsonP12b :: IO ()
--  1. v1 Sup; 2. v1->v1 iImp 1-1. 
-- Huth-Ryan p.13:
-- The rule →i (with conclusion φ → ψ) does not prohibit the possibility that φ and ψ coincide. 
-- They could both be instantiated to p.
thompsonP12b  = -- |- v1->v1
    let 
        gamma   = []
        v1      = Var 1
        (⇒) :: PL->PL->PL
        f⇒g     = Oimp f g
        lpasos  = [ (1,(v1,     Isup,       [(1,0)])), 
                    (2,(v1⇒v1,  Iimp 1 1,   [(1,1)]))
                    ]
        phi     = v1⇒v1
    in showCheckDedNat gamma lpasos phi
--
thompsonP12c1 :: IO ()
-- 1. v2 Sup; 2. v1->v2 iImp 1-1; 3. v2->(v1->v2)
thompsonP12c1 = -- |- v2->(v1->v2) Incorrecta
    let v1= Var 1
        v2= Var 2
        gamma= []
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos = [  (1,(v2,             Isup,       [(1,0)])),  
                    (2,(v1⇒v2,          Iimp 1 1,   [(1,0)])), 
                    (3,(v2⇒(v1⇒v2),     Iimp 1 2,   [(1,1)])) 
                    ] 
        phi = v2⇒(v1⇒v2)
    in showCheckDedNat gamma lpasos phi 
--                
huthRyanP20 :: IO ()
huthRyanP20 = -- |- v2->(v1->v2) Correcta 
    let v1= Var 1
        v2= Var 2
        gamma= []
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos = [  (1,(v2,             Isup,       [(1,0)])), 
                    (2,(v1,             Isup,       [(1,0),(2,0)])), 
                    (3,(v2,             Copy 1,     [(1,0),(2,0)])), 
                    (4,(v1⇒v2,          Iimp 2 3,   [(1,0),(2,3)])), 
                    (5,(v2⇒(v1⇒v2),     Iimp 1 4,   [(1,4),(2,3)]))
                    ]
        phi = v2⇒(v1⇒v2)
    in showCheckDedNat gamma lpasos phi
--
--
huthRyanP8Ej6 :: IO ()
huthRyanP8Ej6 = -- {(v1 ∧ v2) ∧ v3, v4 ∧ v5} |− v2 ∧ v4
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        v4= Var 4
        v5= Var 5
        gamma= [(v1∧v2)∧v3, v4∧v5]
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        lpasos = [  (1,((v1∧v2)∧v3,     Prem,       [])), 
                    (2,(v4∧v5,          Prem,       [])), 
                    (3,(v1∧v2,          Econ1 1,    [])), 
                    (4,(v2,             Econ2 3,    [])),
                    (5,(v4,             Econ1 2,    [])), 
                    (6,(v2∧v4,          Icon 4 5,   []))
                    ]
        phi = v2∧v4
    in showCheckDedNat gamma lpasos phi 


practica02Ej1 :: IO ()
practica02Ej1 = --{|-((A->B) ∧ (B -> C)) -> ((A v B)-> C)}
    let a = Var 1
    let b = Var 2
    let c = Var 3
    gamma = []
    (⇒) :: PL->PL->PL
    f⇒g= Oimp f g
    (∧) :: PL->PL->PL
    f∧g= Oand f g
    (∨) :: PL->PL->PL
    f∨g= Oor f g
    lpasos = [ (1,( (a⇒b) ∧ (b⇒c),    Isup, [(1,0)])),
               (2,( a ∨ b,            Isup, [(1,0),(2,0)])),                 
               (3,( a,                Isup, [(1,0),(2,0),(3,0)])),
               (4,( a⇒b,              Econ1 1, [(1,0),(2,0),(3,0)])),
               (5,( b,                Eimp 4 3, [(1,0),(2,0),(3,0)])),
               (6,( b⇒c,              Econ2 1, [(1,0),(2,0),(3,0)])),
               (7,( c,                Eimp 6 5, [(1,0),(2,0),(3,0)])),
               (8,( a⇒c,              Iimp 3 7, [(1,0),(2,0),(3,7)])),
               (9,( b,                Isup, [(1,0),(2,0),(3,7),(9,0)])),
               (10,( b⇒c              Copy 6, [(1,0),(2,0),(3,7),(9,0)])),    
               (11,( c,               Eimp 10 9, [(1,0),(2,0),(3,7),(9,0)])),
               (12,( b⇒c,             Iimp 9 11, [(1,0),(2,0),(3,7),(9,11)])),
               (13,( c,               Edis 2 8 12, [(1,0),(2,0),(3,7),(9,11)])),
               (14,( (a ∨ b) ⇒ c      Iimp 2 13, [(1,0),(2,13),(3,7),(9,11)])),
               (15,( ((a⇒b) ∧ (b⇒c))⇒ ((a ∨ b) ⇒ c ), Iimp 1 14 [(1,14),(2,13),(3,7),(9,11)]))]
    phi = ((a⇒b) ∧ (b⇒c))⇒ ((a ∨ b) ⇒ c )
     in
    showCheckDedNat gamma lpasos phi

practica02Ej2 :: IO ()
practica02Ej2 = --{(A->B), (B-> C) |- (A->C)}
    let a = Var 1
    let b = Var 2
    let c = Var 3
    gamma = [a⇒b,b⇒c]
    (⇒) :: PL->PL->PL
    f⇒g = Oimp f g
    lpasos = [ (1, (a⇒b,     Prem, [])),
               (2, (b⇒c,     Prem, [])),
               (3, (a,       Isup, [(3,0)])),
               (4, (b,       Eimp 3 1, [(3,0)])),
               (5, (c,       Eimp 4 2, [(3,0)])),
               (6, (a⇒c,     Iimp 3 5, [(3,5)]))]
    phi = a⇒c
     in
    showCheckDedNat gamma lpasos phi

practica02Ej3 :: IO ()
practica02Ej3 = --{|- ((a v b) -> c) -> ((a -> c) ∧ (b -> c))}
    let 
      a = Var 1
      b = Var 2
      c = Var 3
      gamma = []
      (⇒) :: PL->PL->PL
      f⇒g = Oimp f g
      (∧) :: PL->PL->PL
      f∧g = Oand f g
      (∨) :: PL->PL->PL
      f∨g = Oor f g
      lpasos = [ (1, ( (a ∨ b) ⇒ c,   Isup, [(1,0)])),
                 (2, ( a,             Isup, [(1,0),(2,0)])),
                 (3, ( a ∨ b,         Idis1 2, [(1,0),(2,0)])),
                 (4, ( c,             Eimp 3 1, [(1,0),(2,0)])),
                 (5, ( a⇒c,           Iimp 2 4, [(1,0),(2,4)])),
                 (6, ( b,             Isup, [(1,0),(2,4),(6,0)])),
                 (7, ( a ∨ b,         Idis2 6, [(1,0),(2,4),(6,0)])),
                 (8, ( c,             Eimp 7 1, [(1,0),(2,4),(6,0)])),
                 (9, ( b⇒c,           Iimp 6 8, [(1,0),(2,4),(6,8)])),
                 (10 ( (a⇒c) ∧ (b⇒c), Iimp 5 9, [(1,0),(2,4),(6,8)])),
                 (11,( ((a ∨ b)⇒c) ⇒ ((a ⇒ c) ∧ (b ⇒ c)), Iimp 1 10,[(1,10)]))]
    phi = ((a ∨ b)⇒c) ⇒ ((a ⇒ c) ∧ (b ⇒ c))
     in
    showCheckDedNat gamma lpasos phi

practica02Ej4 :: IO ()
practica02Ej4 = --{(A -> (B -> C))-> ((A ∧ B)-> C)}
    let
      a = Var 1
      b = Var 2
      c = Var 3
      gamma = []
      (⇒) :: PL->PL->PL
      f⇒g = Oimp f g
      (∧) :: PL->PL->PL
      f∧g = Oand f g
      lpasos = [ (1, ( (a⇒(b⇒c),      Isup, [(1,0)])),
                 (2, (  a ∧ b,        Isup, [(1,0),(2,0)])),
                 (3, (  a,            Econ1 2, [(1,0),(2,0)])),
                 (4, (  b⇒c,          Eimp 3 1, [(1,0),(2,0)])),
                 (5, (  b,            Econ2 2, [(1,0),(2,0)])),
                 (6, (  c,            Eimp 5 4, [(1,0),(2,0)])),
                 (7, (  (a ∧ b)⇒c,    Iimp 2 6, [(1,0),(2,6)])),
                 (8, (  (a⇒(b⇒c))⇒((a ∧ b)⇒c), Iimp 1 7, [(1,7),(2,6)]))]
      phi = (a⇒(b⇒c))⇒((a ∧ b)⇒c)
       in
      showCheckDedNat gamma lpasos phi

practica02Ej6 :: IO ()
practica02Ej6 =  --{A -> ¬¬A}
    let 
      a = Var 1         
      gamma = []
      (¬) :: PL -> PL
       ¬f = Oneg f
      (⇒) :: PL->PL->PL
      f⇒g = Oimp f g
      lpasos = [ (1, ( a,        Isup, [(1,0)])),
                 (2, ( ¬a,       Isup, [(1,0),(2,0)])),
                 (3, ( Bot,      Eneg 1 2, [(1,0),(2,0)])), 
                 (4, ( ¬¬a,      Ineg 2 3, [(1,0),(2,3)])),
                 (5, ( a⇒¬¬a,    Iimp 1 4, [(1,5),(2,3)]))]
      phi = a⇒¬¬a
       in
      showCheckDedNat gamma lpasos phi

practica02Ej7 :: IO ()
practica02Ej7 = --{((A=>B) => A) => A}
    let
      a = Var 1
      b = Var 2
      gamma = []
      (⇒) :: PL->PL->PL
      f⇒g = Oimp f g
      (¬) :: PL -> PL
       ¬f = Oneg f
      (∨) :: PL->PL->PL
      f∨g = Oor f g
      lpasos = [ (1, ( (a⇒b)⇒a,          Isup, [(1,0)])),
                 (2, ( ¬(¬(a⇒b) ∨ a),    Isup, [(1,0),(2,0)])),
                 (3, ( ¬(a⇒b),           Isup, [(1,0),(2,0),(3,0)])),
                 (4, ( ¬(a⇒b) ∨ a,       Idis1 3, [(1,0),(2,0),(3,0)])),
                 (5, ( Bot,              Eneg 2 4,[(1,0),(2,0),(3,0)])),
                 (6, ( ¬¬(a⇒b),          Ineg 3 5,[(1,0),(2,0),(3,5)])),
                 (7, ( a⇒b,              E2neg 6, [(1,0),(2,0),(3,5)])),
                 (8, ( a,                Isup,    [(1,0),(2,0),(3,5),(8,0)])),
                 (9, ( ¬(a⇒b) ∨ a        Idis2 8, [(1,0),(2,0),(3,5),(8,0)])),
                 (10,( Bot,              Eneg 2 9,[(1,0),(2,0),(3,5),(8,0)])),
                 (11,( ¬a,               Ineg 8 10,[(1,0),(2,0),(3,5),(8,10)])),
                 (12,( a,                Eimp 7 1, [(1,0),(2,0),(3,5),(8,10)])),
                 (13,( Bot               Eneg 11 12,[(1,0),(2,0),(3,5),(8,10)])),
                 (14,( ¬¬(¬(a⇒b) ∨ a),   Ineg 2 13, [(1,0),(2,13),(3,5),(8,10)])),
                 (15,( ¬(a⇒b) ∨ a,       E2neg 14, [(1,0),(2,13),(3,5),(8,10)])),
                 (16,( ¬(a⇒b),           Isup, [(1,0),(2,13),(3,5),(8,10),(16,0)])), 
                 (17,( ¬a,               Isup, [(1,0),(2,13),(3,5),(8,10),(16,0),(17,0)])),
                 (18,( a,                Isup, [(1,0),(2,13),(3,5),(8,10),(16,0),(17,0),(18,0)])),
                 (19,( Bot,              Eneg 2 9, [(1,0),(2,13),(3,5),(8,10),(16,0),(17,0),(18,0)])),   
                 (20,( b,                Ebot 19, [(1,0),(2,13),(3,5),(8,10),(16,0),(17,0),(18,0)])),
                 (21,( a⇒b,              Iimp 18 20, [(1,0),(2,13),(3,5),(8,10),(16,0),(17,0),(18,20)])),
                 (22,( Bot,              Eneg 16 21, [(1,0),(2,13),(3,5),(8,10),(16,0),(17,0),(18,20)])),
                 (23,( ¬¬a,              Ineg 17 22, [(1,0),(2,13),(3,5),(8,10),(16,0),(17,21),(18,20)])),
                 (24,( a,                E2neg 23, [(1,0),(2,13),(3,5),(8,10),(16,0),(17,21),(18,20)])),
                 (25,( ¬(a⇒b)⇒a,         Iimp 16 24, [(1,0),(2,13),(3,5),(8,10),(16,24),(17,21),(18,20)])),
                 (26,( a,                Isup, [(1,0),(2,13),(3,5),(8,10),(16,24),(17,21),(18,20),(26,0)])),
                 (27,( a⇒a,              Iimp, [(1,0),(2,13),(3,5),(8,10),(16,24),(17,21),(18,20),(26,26)])),
                 (28,( a                 Edis 15 25 27, [(1,0),(2,13),(3,5),(8,10),(16,24),(17,21),(18,20),(26,26)])),
                 (29,( ((a⇒b)⇒a)⇒a       Iimp, [(1,28),(2,13),(3,5),(8,10),(16,24),(17,21),(18,20),(26,26)]))]
      phi = ((a⇒b)⇒a)⇒a
       in
      showCheckDedNat gamma lpasos phi  