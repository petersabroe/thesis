Definition Hiding_real p : 
    game (ICommitment p) := 
    [module no_locs ;
       #def #[ COMMITMENT ] (v : 'value p) : ('commitment p)
        {
          k ← p.(setup) ;;
          _ ← p.(sampl_value) ;;
          '(c, o) ← p.(commit) k v ;;
          @ret ('commitment p) c 
        }
    ].

Definition Hiding_ideal p : 
    game (ICommitment p) := 
    [module no_locs ; 
       #def #[ COMMITMENT ] (v : 'value p) : ('commitment p)
        {
          k ← p.(setup) ;;
          u ← p.(sampl_value) ;;
          '(c, o) ← p.(commit) k u ;;           
          @ret ('commitment p) c 
        }
    ].