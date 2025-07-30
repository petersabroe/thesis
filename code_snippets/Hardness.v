Definition Hardness (p: raw_sigExt) b :
  game (IHardness p) :=
  [module fset [:: key_loc (sig_to_com p) ] ;
    #def #[ INIT ] (_ : 'unit) : ('unit) 
      {
        h ← (sig_to_com p).(setup) ;;
        #put key_loc (sig_to_com p) := Some h ;;
        ret tt 
      } ;
    #def #[ GET ] (_ : 'unit) : ('key (sig_to_com p)) 
      {
        h ← getSome (key_loc (sig_to_com p));; 
        ret h
      } ;
    #def #[ QUERY ] (w : 'witness p) : 'bool 
      {
        h ← getSome (key_loc (sig_to_com p));; 
        @ret 'bool (b && (p.(R) h w))
      }
  ].