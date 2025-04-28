Record raw_sigCom := 
  { p :> raw_sigma 
  ; sampl_wit : 
      code no_locs [interface] (Witness p) 

  ; sampl_challenge : 
      code no_locs [interface] (Challenge p) 

  ; key_gen :  ∀ (w : Witness p),
      code no_locs [interface] (Statement p)
  }.


Definition sig_to_com (p : raw_sigCom) : raw_com :=
  {| Key := p.(Statement)
   ; Value := p.(Challenge) 
   ; Commitment := p.(Message) 
   ; Opening := p.(Response)
 
   ; setup := 
     {code 
       w ← p.(sampl_wit) ;; 
       h ← (p.(key_gen) w) ;;
       #assert p.(R) h w ;;
       ret ((h) : _)
      }

   ; commit := λ k u,
     {code
       '(a, z) ← p.(simulate) k u ;;
       ret ((a, z) : (_ × _))
     }

   ; verify := λ k c v d,
     {code 
        ret (p.(Sigma.verify) k c v d)%B
     }

   ; sampl_value := p.(sampl_challenge)

  |}.