`ifndef COMMON_VH
`define COMMON_VH

// returns ceiling of the log base 2 of the input
function integer clogb2 (input integer bit_depth);
        begin
                for(clogb2=0; bit_depth>0; clogb2=clogb2+1)
                        bit_depth = bit_depth >> 1;
        end
endfunction

`endif
