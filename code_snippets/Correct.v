Definition Correct_real p : 
    game (ICorrect_com p) :=
    [module no_locs ;
       #def #[ CORRECTNESS ] (v : 'value p) : ('bool) 
        {
          k ← p.(setup) ;;
          '(c, o) ← p.(commit) k v ;;
          b ← p.(verify) k c v o ;;
          ret b

        }
    ].


Definition Correct_ideal p : 
    game (ICorrect_com p) :=
    [module no_locs ;
       #def #[ CORRECTNESS ] (v : 'value p) : ('bool) 
        {
          k ← p.(setup) ;;
          ret true
        }
    ].
