Definition Hiding_real p : 
    game (ICommitment p) := 
    [module no_locs ;
       #def #[ COMMITMENT ] (v : 'value p) : ('commitment p)
        {
          k ← p.(setup) ;;
          '(c, o) ← p.(commit) k v ;;
          @ret ('commitment p) c 
        }
    ].