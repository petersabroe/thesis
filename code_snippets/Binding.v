Definition Binding_real p : 
    game (IBinding p) := 
    [module no_locs ;
        #def #[ BINDING ] ('(c, v, o, v', o') : 'binding p) : 'bool
        { 
          k ← p.(setup) ;;
          b ← p.(verify) k c v o ;;
          b' ← p.(verify) k c v' o' ;; 
          #assert b ;;
          #assert b' ;;
          #assert (v != v') ;;
          @ret 'bool true 
        }
    ].

Definition Binding_ideal p :
     game (IBinding p) := 
    [module no_locs ;
        #def #[ BINDING ] ('(c, v, o, v', o') : 'binding p) : 'bool
        {
          k ← p.(setup) ;;
          p.(verify) k c v o ;;
          p.(verify) k c v' o' ;; 
          @ret 'bool true
        }
    ].