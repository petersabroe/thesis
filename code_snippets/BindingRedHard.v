Definition Call_Hardness (p: raw_sigExt) :
   module (IHardness p) (IBinding (sig_to_com p)) :=
  [module no_locs ;
      #def #[ INIT ] (_ : 'unit) : ('unit) {
        #import {sig #[ INIT ] : 'unit → 'unit} as INITH ;;
        u ← INITH Datatypes.tt ;;
        ret u
      } ;

      #def #[ GET ] (_ : 'unit) : ('key (sig_to_com p)) 
        {
          #import {sig #[ GET ] : 'unit → 'statement p} as GETH ;;
          h ← GETH Datatypes.tt ;;
          ret h
        } ;
      #def #[ BINDING ] ('(c, v, o, v', o') : 'binding (sig_to_com p)) : 'bool
          {
            #import {sig #[ QUERY ] : ('witness p) → 'bool} as QUE ;;
            #import {sig #[ GET ] : 'unit → 'statement p} as GETH ;;
            h ← GETH tt ;;
            let b := p.(Sigma.verify) h c v o in
            let b' := p.(Sigma.verify) h c v' o' in
            let b'' := (v != v') in
            let ow := p.(extractor) h c v v' o o' in
            if ow is Some w 
              then 'b''' ← QUE w ;; ret (b''' && b && b' && b'') 
              else ret false
          }
    ].