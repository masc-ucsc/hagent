bind bitcnt bitcnt_prop
  #() u_bitcnt_sva(   .din_data(bitcnt.din_data),
   .din_func(bitcnt.din_func),
   .dout_data(bitcnt.dout_data),
   .tmp(bitcnt.tmp),
   .cnt(bitcnt.cnt),
   .mode32(bitcnt.mode32),
   .czmode(bitcnt.czmode)); 
