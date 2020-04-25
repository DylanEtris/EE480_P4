// some basic sizes of things
`define DATA	[15:0]
`define ADDR	[15:0] //address
`define INST	[15:0] //instruction
`define SIZE	[65535:0]
`define STATE	[7:0]  //state number size & opcode size
`define REGS	[15:0] //size of registers
`define REGNAME	[3:0]  //16 registers to choose from
`define WORD	[15:0] //16-bit words
`define HALF	[7:0]	//8-bit half-words
`define NIB		[3:0]	//4-bit nibble
`define HI8		[15:8]
`define LO8		[7:0]
`define HIGH8	[15:8]
`define HIGH4 [15:12]
`define LOW8	[7:0]

// the instruction fields
`define F_H		[15:12] //4-bit header (needed for short opcodes)
`define F_OP	[15:8]
`define F_D		[3:0]
`define F_S		[7:4]
`define F_C8	[11:4]
`define F_ADDR	[11:4]

//long instruction headers
`define HCI8	4'hb
`define HCII	4'hc
`define HCUP	4'hd
`define HBNZ	4'hf
`define HBZ		4'he

// opcode values, also state numbers
`define OPADDI	8'h70
`define OPADDII	8'h71
`define OPMULI	8'h72
`define OPMULII	8'h73
`define OPSHI	8'h74
`define OPSHII	8'h75
`define OPSLTI	8'h76
`define OPSLTII	8'h77

`define OPADDF	8'h60
`define OPADDPP	8'h61
`define OPMULF	8'h62
`define OPMULPP	8'h63

`define OPAND	8'h50
`define OPOR	8'h51
`define OPXOR	8'h52
`define OPDUP   8'h53

`define OPLD	8'h40
`define OPST	8'h41

`define OPANYI	8'h30
`define OPANYII	8'h31
`define OPNEGI	8'h32
`define OPNEGII	8'h33
`define OPNEGF  8'h34

//These have been changed, need to update .aik
`define OPF2I   8'h17
`define OPI2F   8'h18
`define OPII2PP 8'h19
`define OPF2PP	8'h21
`define OPPP2F	8'h22
`define OPPP2II 8'h23
`define OPINVF	8'h24
`define OPINVPP	8'h25

`define OPNOT	8'h10

`define OPJR	8'h01

`define OPTRAP	8'h00

`define OPCI8	8'hbz
`define OPCII	8'hc?
`define OPCUP	8'hdz

`define OPBZ	8'hez
`define OPBNZ	8'hfz

`define NOP 	8'h02

//Definitions for Dr. Dietz modules
// Field definitions
`define	WORD	[15:0]	// generic machine word size
`define	INT	signed [15:0]	// integer size
`define FLOAT	[15:0]	// half-precision float size
`define FSIGN	[15]	// sign bit
`define FEXP	[14:7]	// exponent
`define FFRAC	[6:0]	// fractional part (leading 1 implied)

// Constants
`define	FZERO	16'b0	  // float 0
`define F32767  16'h46ff  // closest approx to 32767, actually 32640
`define F32768  16'hc700  // -32768

// Given by Dr. Dietz
// Integer to float conversion, 16 bit
module i2f(f, i);
output wire `FLOAT f;
input wire `INT i;
wire [4:0] lead;
wire `WORD pos;
assign pos = (i[15] ? (-i) : i);
lead0s m0(lead, pos);
assign f `FFRAC = (i ? ({pos, 8'b0} >> (16 - lead)) : 0);
assign f `FSIGN = i[15];
assign f `FEXP = (i ? (128 + (14 - lead)) : 0);
endmodule

// Given by Dr. Dietz
// Float set-less-than, 16-bit (1-bit result) torf=a<b
module fslt(torf, a, b);
output wire torf;
input wire `FLOAT a, b;
assign torf = (a `FSIGN && !(b `FSIGN)) ||
	      (a `FSIGN && b `FSIGN && (a[14:0] > b[14:0])) ||
	      (!(a `FSIGN) && !(b `FSIGN) && (a[14:0] < b[14:0]));
endmodule

// Given by Dr. Dietz
// Float to integer conversion, 16 bit
// Note: out-of-range values go to -32768 or 32767
module f2i(i, f);
output wire `INT i;
input wire `FLOAT f;
wire `FLOAT ui;
wire tiny, big;
fslt m0(tiny, f, `F32768);
fslt m1(big, `F32767, f);
assign ui = {1'b1, f `FFRAC, 16'b0} >> ((128+22) - f `FEXP);
assign i = (tiny ? 0 : (big ? 32767 : (f `FSIGN ? (-ui) : ui)));
endmodule

module processor(halt, reset, clk);
output reg halt;
input reset, clk;

reg `DATA r `REGS;	// register file
reg `DATA dm `SIZE;	// data memory
reg `INST im `SIZE;	// instruction memory
reg `ADDR pc;
wire `ADDR tpc;
reg `INST ir;
reg `HALF op0, op1;
reg `NIB d0, d1;
reg `DATA dv1, dv2;
reg `NIB s0, s1;
reg `DATA sv1;
reg `HALF const0, const1;
reg jump;
wire zflag;		// z flag
wire pendz;
wire wait1;
wire `WORD f2iOut, i2fOut;
	
reg `DATA target;	// target for branch or jump

	i2f myi2f(i2fOut,dv1);
	f2i myf2i(f2iOut, dv1);
	assign zflag = (dv1 == 0);
	assign pendz = (op0 == `OPTRAP && (op1 [7:4] === 4'hf || op1 [7:4] == 4'he || op1 == `OPJR));
	assign wait1 = (d0 == d1 || s0 == d1 || s0 == s1 || (op0 == `OPTRAP && (op1 == `OPBZ || op1 == `OPBNZ)));
	assign tpc = (jump ? target : pc);

always @(reset) begin
	halt <= 0;
	pc <= 0;
	op0 <= `NOP; op1 <= `NOP;
	jump <= 0;

	//Load vmem files
	$readmemh0(im);
	//readmemh1(dm);
end

//stage 0: instruction fetch
always @(posedge clk) begin
	if (wait1 || pendz) begin
		pc <= tpc;
		//wait
	end else begin
		//not blocked by stage 1
		op0 <= im[tpc] `F_OP;
		d0 <= im[tpc] `F_D;
		s0 <= im[tpc] `F_S;
		const0 <= im[tpc] `F_C8;
		pc <= tpc + 1;
	end
end

//stage 1: register read
always @(posedge clk) begin
	if (wait1 || pendz || jump) begin
    		// stall waiting for register value
		op1 <= `NOP;
		dv1 <= r[d0];
		d1 <= 4'bz;
    		sv1 <= r[s0];
  	end else begin
    		// all good, get operands (even if not needed)
		const1 <= const0;
    		dv1 <= r[d0];
		d1 <= d0;
    		sv1 <= r[s0];
    		op1 <= op0;
  end

end

//stage 2: ALU, data memory access, reg write
always @(posedge clk) begin
	if ((op1 == `NOP)) begin
		// condition says nothing happens
		jump <= 0;
	end else begin
		casez (op1)
			`OPADDI: begin r[d1] <= dv1 + sv1; end
			//IMPLEMENT FLOATING POINT
			`OPADDF: begin r[d1] <= dv1 + sv1; end
			`OPADDII: begin r[d1] `HI8 <= dv1 `HI8 + sv1 `HI8; r[d1] `LO8 = dv1 `LO8 + sv1 `LO8; end
			//IMPLEMENT POSIT
			`OPADDPP: begin r[d1] `HI8 <= dv1 `HI8 + sv1 `HI8; r[d1] `LO8 = dv1 `LO8 + sv1 `LO8; end
			`OPMULI: begin r[d1] <= dv1 * sv1; end
			//NEW
			`OPMULF: begin r[d1] <= dv1 * sv1; end
			`OPMULII: begin r[d1] <= dv1 * sv1; r[d1]`HI8 = dv1 `HI8 * sv1`HI8; end
			//IMPLEMENT POSIT
			`OPMULPP: begin r[d1] <= dv1 * sv1; r[d1]`HI8 = dv1 `HI8 * sv1`HI8; end
			`OPAND: begin r[d1] <= dv1 & sv1; end
			`OPOR: begin r[d1] <= dv1 | sv1; end
			`OPXOR: begin r[d1] <= dv1 ^ sv1; end
			//NEW
			`OPDUP: begin r[d1] <= sv1; end
			`OPSHI: begin r[d1] <= (sv1 > 32767 ? dv1 >> -sv1 : dv1 << sv1); end
			`OPNOT: begin r[d1] <= ~dv1; end
			`OPANYI: begin r[d1] <= (dv1 ? -1 : 0); end
			`OPANYII: begin r[d1] `HI8 <= (dv1 `HI8 ? -1 : 0); r[d1] `LO8 <= (dv1 `LO8 ? -1 : 0); end
			`OPLD:  begin r[d1] <= dm[sv1]; end
			`OPSLTI: begin r[d1] <= dv1 < sv1; end
			`OPSLTII: begin r[d1] `HIGH8 <= dv1 `HIGH8 < sv1 `HIGH8; r[d1] `LOW8 <= dv1 `LOW8 < sv1 `LOW8; end
			//NEW, no OP yet
			`OPF2I: begin r[d1] <= f2iOut; end
			//NEW, no OP yet
			`OPF2PP: begin r[d1] <= dv1; end
			//NEW
			`OPI2F: begin r[d1] <= i2fOut; end
			//IMPLEMENT POSIT
			`OPII2PP: begin r[d1] <= dv1; end
			//IMPLEMENT POSIT
			`OPPP2II: begin r[d1] <= dv1; end
			//NEW
			`OPPP2F: begin r[d1] <= dv1; end
			//NEW
			`OPINVF: begin r[d1] <= (dv1 == 1 ? 1 : 0); end
			`OPINVPP: begin r[d1] `HI8 <= (dv1 `HI8 == 1 ? 1 : 0); r[d1] `LO8 <= (dv1 `LO8 == 1 ? 1 : 0); end
			`OPNEGI: begin r[d1] <= -dv1; end
			`OPNEGII: begin r[d1] `HI8 <= -dv1 `HI8; r[d1] `LO8 <= -dv1 `LO8; end
			//NEW
			`OPNEGF: begin r[d1] <= -dv1 end
			`OPCI8:	begin r[d1] <=  ((const1 & 8'h80) ? 16'hff00 : 0) | (const1 & 8'hff); end
			`OPCII: begin r[d1] `HI8 <= const1; r[d1] `LO8 <= const1; end
			`OPCUP: begin r[d1] `HI8 <= const1; end
			`OPSHII: begin r[d1] `LO8 <= (sv1`LO8 > 127 ? dv1 `LO8 >> -sv1`LO8 : dv1 `LO8 << sv1`LO8); 
				r[d1] `HI8 <= (sv1`HI8 > 127 ? dv1 `HI8 >> -sv1`HI8 : dv1 `HI8 << sv1`HI8); end
			`OPST:  begin dm[sv1] <= dv1; end // this may be wrong
			`OPLD:  begin r[d1] = dm[sv1]; end
			`OPBZ: begin
				if (zflag != 0) begin
					jump <= 1;
					target <= const1 + pc - 2;
				end
			end
			`OPBNZ: begin
				if (zflag == 0) begin
					jump <= 1;
					target <= const1 + pc - 2;
				end
			end
			`OPJR: begin
				jump <= 1;
				target <= dv1;
			end
			default: halt <= 1;
		endcase
	end
end
endmodule



module testbench;
reg reset = 0;
reg clk = 0;
wire halted;
processor PE(halted, reset, clk);
initial begin
  $dumpfile;
  $dumpvars(0, PE);
  #10 reset = 1;
  #10 reset = 0;
  while (!halted) begin
    #10 clk = 1;
    #10 clk = 0;
  end
  $finish;
end
endmodule
