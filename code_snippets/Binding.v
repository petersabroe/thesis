Definition Binding_real p : 
    game (IBinding p) := 
      [module fset [:: key_loc p ] ;
        #def #[ INIT ] (_ : 'unit) : ('unit) {
          'k ← p.(setup) ;;
          #put key_loc p := Some k ;;
          ret tt
        } ;

        #def #[ GET ] (_ : 'unit) : ('key p) {
          k ← getSome key_loc p ;;
          ret k
        } ;

        #def #[ BINDING ] ('(c, v, o, v', o') : 'binding p) : 'bool
        { 
          k ← getSome key_loc p ;;
          b ← p.(verify) k c v o ;;
          b' ← p.(verify) k c v' o' ;; 
          let b'' := (v != v') in
          @ret 'bool (b && b' && b'')

        }
    ].

Definition Binding_ideal p :
     game (IBinding p) := 
       [module fset [:: key_loc p ] ;
        #def #[ INIT ] (_ : 'unit) : ('unit) {
          'k ← p.(setup) ;;
          #put key_loc p := Some k ;;
          ret tt
        } ;

        #def #[ GET ] (_ : 'unit) : ('key p) {
          k ← getSome key_loc p ;;
          ret k
        } ;

        #def #[ BINDING ] ('(c, v, o, v', o') : 'binding p) : 'bool
        {
          k ← getSome key_loc p ;;
          b ← p.(verify) k c v o ;;
          b' ← p.(verify) k c v' o' ;;
          let b'' := (v != v') in
          @ret 'bool (false && b && b' && b'')
        }
    ].