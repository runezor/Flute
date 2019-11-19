//
// Generated by Bluespec Compiler, version 2019.05.beta1 (build b38abf678, 2019-05-06)
//
//
//
//
// Ports:
// Name                         I/O  size props
// slave_awready                  O     1 reg
// slave_wready                   O     1 reg
// slave_bvalid                   O     1 reg
// slave_bid                      O     4 reg
// slave_bresp                    O     2 reg
// slave_arready                  O     1 reg
// slave_rvalid                   O     1 reg
// slave_rid                      O     4 reg
// slave_rdata                    O    64 reg
// slave_rresp                    O     2 reg
// slave_rlast                    O     1 reg
// master_awvalid                 O     1 reg
// master_awid                    O     4 reg
// master_awaddr                  O    64 reg
// master_awlen                   O     8 reg
// master_awsize                  O     3 reg
// master_awburst                 O     2 reg
// master_awlock                  O     1 reg
// master_awcache                 O     4 reg
// master_awprot                  O     3 reg
// master_awqos                   O     4 reg
// master_awregion                O     4 reg
// master_wvalid                  O     1 reg
// master_wdata                   O    64 reg
// master_wstrb                   O     8 reg
// master_wlast                   O     1 reg
// master_bready                  O     1 reg
// master_arvalid                 O     1 reg
// master_arid                    O     4 reg
// master_araddr                  O    64 reg
// master_arlen                   O     8 reg
// master_arsize                  O     3 reg
// master_arburst                 O     2 reg
// master_arlock                  O     1 reg
// master_arcache                 O     4 reg
// master_arprot                  O     3 reg
// master_arqos                   O     4 reg
// master_arregion                O     4 reg
// master_rready                  O     1 reg
// trace_data_out_get             O   427 reg
// RDY_trace_data_out_get         O     1 reg
// CLK                            I     1 clock
// RST_N                          I     1 reset
// slave_awvalid                  I     1
// slave_awid                     I     4 reg
// slave_awaddr                   I    64 reg
// slave_awlen                    I     8 reg
// slave_awsize                   I     3 reg
// slave_awburst                  I     2 reg
// slave_awlock                   I     1 reg
// slave_awcache                  I     4 reg
// slave_awprot                   I     3 reg
// slave_awqos                    I     4 reg
// slave_awregion                 I     4 reg
// slave_wvalid                   I     1
// slave_wdata                    I    64 reg
// slave_wstrb                    I     8 reg
// slave_wlast                    I     1 reg
// slave_bready                   I     1
// slave_arvalid                  I     1
// slave_arid                     I     4 reg
// slave_araddr                   I    64 reg
// slave_arlen                    I     8 reg
// slave_arsize                   I     3 reg
// slave_arburst                  I     2 reg
// slave_arlock                   I     1 reg
// slave_arcache                  I     4 reg
// slave_arprot                   I     3 reg
// slave_arqos                    I     4 reg
// slave_arregion                 I     4 reg
// slave_rready                   I     1
// master_awready                 I     1
// master_wready                  I     1
// master_bvalid                  I     1
// master_bid                     I     4 reg
// master_bresp                   I     2 reg
// master_arready                 I     1
// master_rvalid                  I     1
// master_rid                     I     4 reg
// master_rdata                   I    64 reg
// master_rresp                   I     2 reg
// master_rlast                   I     1 reg
// EN_trace_data_out_get          I     1
//
// No combinational paths from inputs to outputs
//
//

`ifdef BSV_ASSIGNMENT_DELAY
`else
  `define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif

module mkDM_Mem_Tap(CLK,
		    RST_N,

		    slave_awvalid,
		    slave_awid,
		    slave_awaddr,
		    slave_awlen,
		    slave_awsize,
		    slave_awburst,
		    slave_awlock,
		    slave_awcache,
		    slave_awprot,
		    slave_awqos,
		    slave_awregion,

		    slave_awready,

		    slave_wvalid,
		    slave_wdata,
		    slave_wstrb,
		    slave_wlast,

		    slave_wready,

		    slave_bvalid,

		    slave_bid,

		    slave_bresp,

		    slave_bready,

		    slave_arvalid,
		    slave_arid,
		    slave_araddr,
		    slave_arlen,
		    slave_arsize,
		    slave_arburst,
		    slave_arlock,
		    slave_arcache,
		    slave_arprot,
		    slave_arqos,
		    slave_arregion,

		    slave_arready,

		    slave_rvalid,

		    slave_rid,

		    slave_rdata,

		    slave_rresp,

		    slave_rlast,

		    slave_rready,

		    master_awvalid,

		    master_awid,

		    master_awaddr,

		    master_awlen,

		    master_awsize,

		    master_awburst,

		    master_awlock,

		    master_awcache,

		    master_awprot,

		    master_awqos,

		    master_awregion,

		    master_awready,

		    master_wvalid,

		    master_wdata,

		    master_wstrb,

		    master_wlast,

		    master_wready,

		    master_bvalid,
		    master_bid,
		    master_bresp,

		    master_bready,

		    master_arvalid,

		    master_arid,

		    master_araddr,

		    master_arlen,

		    master_arsize,

		    master_arburst,

		    master_arlock,

		    master_arcache,

		    master_arprot,

		    master_arqos,

		    master_arregion,

		    master_arready,

		    master_rvalid,
		    master_rid,
		    master_rdata,
		    master_rresp,
		    master_rlast,

		    master_rready,

		    EN_trace_data_out_get,
		    trace_data_out_get,
		    RDY_trace_data_out_get);
  input  CLK;
  input  RST_N;

  // action method slave_m_awvalid
  input  slave_awvalid;
  input  [3 : 0] slave_awid;
  input  [63 : 0] slave_awaddr;
  input  [7 : 0] slave_awlen;
  input  [2 : 0] slave_awsize;
  input  [1 : 0] slave_awburst;
  input  slave_awlock;
  input  [3 : 0] slave_awcache;
  input  [2 : 0] slave_awprot;
  input  [3 : 0] slave_awqos;
  input  [3 : 0] slave_awregion;

  // value method slave_m_awready
  output slave_awready;

  // action method slave_m_wvalid
  input  slave_wvalid;
  input  [63 : 0] slave_wdata;
  input  [7 : 0] slave_wstrb;
  input  slave_wlast;

  // value method slave_m_wready
  output slave_wready;

  // value method slave_m_bvalid
  output slave_bvalid;

  // value method slave_m_bid
  output [3 : 0] slave_bid;

  // value method slave_m_bresp
  output [1 : 0] slave_bresp;

  // value method slave_m_buser

  // action method slave_m_bready
  input  slave_bready;

  // action method slave_m_arvalid
  input  slave_arvalid;
  input  [3 : 0] slave_arid;
  input  [63 : 0] slave_araddr;
  input  [7 : 0] slave_arlen;
  input  [2 : 0] slave_arsize;
  input  [1 : 0] slave_arburst;
  input  slave_arlock;
  input  [3 : 0] slave_arcache;
  input  [2 : 0] slave_arprot;
  input  [3 : 0] slave_arqos;
  input  [3 : 0] slave_arregion;

  // value method slave_m_arready
  output slave_arready;

  // value method slave_m_rvalid
  output slave_rvalid;

  // value method slave_m_rid
  output [3 : 0] slave_rid;

  // value method slave_m_rdata
  output [63 : 0] slave_rdata;

  // value method slave_m_rresp
  output [1 : 0] slave_rresp;

  // value method slave_m_rlast
  output slave_rlast;

  // value method slave_m_ruser

  // action method slave_m_rready
  input  slave_rready;

  // value method master_m_awvalid
  output master_awvalid;

  // value method master_m_awid
  output [3 : 0] master_awid;

  // value method master_m_awaddr
  output [63 : 0] master_awaddr;

  // value method master_m_awlen
  output [7 : 0] master_awlen;

  // value method master_m_awsize
  output [2 : 0] master_awsize;

  // value method master_m_awburst
  output [1 : 0] master_awburst;

  // value method master_m_awlock
  output master_awlock;

  // value method master_m_awcache
  output [3 : 0] master_awcache;

  // value method master_m_awprot
  output [2 : 0] master_awprot;

  // value method master_m_awqos
  output [3 : 0] master_awqos;

  // value method master_m_awregion
  output [3 : 0] master_awregion;

  // value method master_m_awuser

  // action method master_m_awready
  input  master_awready;

  // value method master_m_wvalid
  output master_wvalid;

  // value method master_m_wdata
  output [63 : 0] master_wdata;

  // value method master_m_wstrb
  output [7 : 0] master_wstrb;

  // value method master_m_wlast
  output master_wlast;

  // value method master_m_wuser

  // action method master_m_wready
  input  master_wready;

  // action method master_m_bvalid
  input  master_bvalid;
  input  [3 : 0] master_bid;
  input  [1 : 0] master_bresp;

  // value method master_m_bready
  output master_bready;

  // value method master_m_arvalid
  output master_arvalid;

  // value method master_m_arid
  output [3 : 0] master_arid;

  // value method master_m_araddr
  output [63 : 0] master_araddr;

  // value method master_m_arlen
  output [7 : 0] master_arlen;

  // value method master_m_arsize
  output [2 : 0] master_arsize;

  // value method master_m_arburst
  output [1 : 0] master_arburst;

  // value method master_m_arlock
  output master_arlock;

  // value method master_m_arcache
  output [3 : 0] master_arcache;

  // value method master_m_arprot
  output [2 : 0] master_arprot;

  // value method master_m_arqos
  output [3 : 0] master_arqos;

  // value method master_m_arregion
  output [3 : 0] master_arregion;

  // value method master_m_aruser

  // action method master_m_arready
  input  master_arready;

  // action method master_m_rvalid
  input  master_rvalid;
  input  [3 : 0] master_rid;
  input  [63 : 0] master_rdata;
  input  [1 : 0] master_rresp;
  input  master_rlast;

  // value method master_m_rready
  output master_rready;

  // actionvalue method trace_data_out_get
  input  EN_trace_data_out_get;
  output [426 : 0] trace_data_out_get;
  output RDY_trace_data_out_get;

  // signals for module outputs
  wire [426 : 0] trace_data_out_get;
  wire [63 : 0] master_araddr, master_awaddr, master_wdata, slave_rdata;
  wire [7 : 0] master_arlen, master_awlen, master_wstrb;
  wire [3 : 0] master_arcache,
	       master_arid,
	       master_arqos,
	       master_arregion,
	       master_awcache,
	       master_awid,
	       master_awqos,
	       master_awregion,
	       slave_bid,
	       slave_rid;
  wire [2 : 0] master_arprot, master_arsize, master_awprot, master_awsize;
  wire [1 : 0] master_arburst, master_awburst, slave_bresp, slave_rresp;
  wire RDY_trace_data_out_get,
       master_arlock,
       master_arvalid,
       master_awlock,
       master_awvalid,
       master_bready,
       master_rready,
       master_wlast,
       master_wvalid,
       slave_arready,
       slave_awready,
       slave_bvalid,
       slave_rlast,
       slave_rvalid,
       slave_wready;

  // ports of submodule f_trace_data
  wire [426 : 0] f_trace_data$D_IN, f_trace_data$D_OUT;
  wire f_trace_data$CLR,
       f_trace_data$DEQ,
       f_trace_data$EMPTY_N,
       f_trace_data$ENQ,
       f_trace_data$FULL_N;

  // ports of submodule master_xactor_f_rd_addr
  wire [96 : 0] master_xactor_f_rd_addr$D_IN, master_xactor_f_rd_addr$D_OUT;
  wire master_xactor_f_rd_addr$CLR,
       master_xactor_f_rd_addr$DEQ,
       master_xactor_f_rd_addr$EMPTY_N,
       master_xactor_f_rd_addr$ENQ,
       master_xactor_f_rd_addr$FULL_N;

  // ports of submodule master_xactor_f_rd_data
  wire [70 : 0] master_xactor_f_rd_data$D_IN, master_xactor_f_rd_data$D_OUT;
  wire master_xactor_f_rd_data$CLR,
       master_xactor_f_rd_data$DEQ,
       master_xactor_f_rd_data$EMPTY_N,
       master_xactor_f_rd_data$ENQ,
       master_xactor_f_rd_data$FULL_N;

  // ports of submodule master_xactor_f_wr_addr
  wire [96 : 0] master_xactor_f_wr_addr$D_IN, master_xactor_f_wr_addr$D_OUT;
  wire master_xactor_f_wr_addr$CLR,
       master_xactor_f_wr_addr$DEQ,
       master_xactor_f_wr_addr$EMPTY_N,
       master_xactor_f_wr_addr$ENQ,
       master_xactor_f_wr_addr$FULL_N;

  // ports of submodule master_xactor_f_wr_data
  wire [72 : 0] master_xactor_f_wr_data$D_IN, master_xactor_f_wr_data$D_OUT;
  wire master_xactor_f_wr_data$CLR,
       master_xactor_f_wr_data$DEQ,
       master_xactor_f_wr_data$EMPTY_N,
       master_xactor_f_wr_data$ENQ,
       master_xactor_f_wr_data$FULL_N;

  // ports of submodule master_xactor_f_wr_resp
  wire [5 : 0] master_xactor_f_wr_resp$D_IN, master_xactor_f_wr_resp$D_OUT;
  wire master_xactor_f_wr_resp$CLR,
       master_xactor_f_wr_resp$DEQ,
       master_xactor_f_wr_resp$EMPTY_N,
       master_xactor_f_wr_resp$ENQ,
       master_xactor_f_wr_resp$FULL_N;

  // ports of submodule slave_xactor_f_rd_addr
  wire [96 : 0] slave_xactor_f_rd_addr$D_IN, slave_xactor_f_rd_addr$D_OUT;
  wire slave_xactor_f_rd_addr$CLR,
       slave_xactor_f_rd_addr$DEQ,
       slave_xactor_f_rd_addr$EMPTY_N,
       slave_xactor_f_rd_addr$ENQ,
       slave_xactor_f_rd_addr$FULL_N;

  // ports of submodule slave_xactor_f_rd_data
  wire [70 : 0] slave_xactor_f_rd_data$D_IN, slave_xactor_f_rd_data$D_OUT;
  wire slave_xactor_f_rd_data$CLR,
       slave_xactor_f_rd_data$DEQ,
       slave_xactor_f_rd_data$EMPTY_N,
       slave_xactor_f_rd_data$ENQ,
       slave_xactor_f_rd_data$FULL_N;

  // ports of submodule slave_xactor_f_wr_addr
  wire [96 : 0] slave_xactor_f_wr_addr$D_IN, slave_xactor_f_wr_addr$D_OUT;
  wire slave_xactor_f_wr_addr$CLR,
       slave_xactor_f_wr_addr$DEQ,
       slave_xactor_f_wr_addr$EMPTY_N,
       slave_xactor_f_wr_addr$ENQ,
       slave_xactor_f_wr_addr$FULL_N;

  // ports of submodule slave_xactor_f_wr_data
  wire [72 : 0] slave_xactor_f_wr_data$D_IN, slave_xactor_f_wr_data$D_OUT;
  wire slave_xactor_f_wr_data$CLR,
       slave_xactor_f_wr_data$DEQ,
       slave_xactor_f_wr_data$EMPTY_N,
       slave_xactor_f_wr_data$ENQ,
       slave_xactor_f_wr_data$FULL_N;

  // ports of submodule slave_xactor_f_wr_resp
  wire [5 : 0] slave_xactor_f_wr_resp$D_IN, slave_xactor_f_wr_resp$D_OUT;
  wire slave_xactor_f_wr_resp$CLR,
       slave_xactor_f_wr_resp$DEQ,
       slave_xactor_f_wr_resp$EMPTY_N,
       slave_xactor_f_wr_resp$ENQ,
       slave_xactor_f_wr_resp$FULL_N;

  // rule scheduling signals
  wire CAN_FIRE_RL_rl_connect,
       CAN_FIRE_RL_rl_connect_1,
       CAN_FIRE_RL_rl_connect_2,
       CAN_FIRE_RL_write_reqs,
       CAN_FIRE_master_m_arready,
       CAN_FIRE_master_m_awready,
       CAN_FIRE_master_m_bvalid,
       CAN_FIRE_master_m_rvalid,
       CAN_FIRE_master_m_wready,
       CAN_FIRE_slave_m_arvalid,
       CAN_FIRE_slave_m_awvalid,
       CAN_FIRE_slave_m_bready,
       CAN_FIRE_slave_m_rready,
       CAN_FIRE_slave_m_wvalid,
       CAN_FIRE_trace_data_out_get,
       WILL_FIRE_RL_rl_connect,
       WILL_FIRE_RL_rl_connect_1,
       WILL_FIRE_RL_rl_connect_2,
       WILL_FIRE_RL_write_reqs,
       WILL_FIRE_master_m_arready,
       WILL_FIRE_master_m_awready,
       WILL_FIRE_master_m_bvalid,
       WILL_FIRE_master_m_rvalid,
       WILL_FIRE_master_m_wready,
       WILL_FIRE_slave_m_arvalid,
       WILL_FIRE_slave_m_awvalid,
       WILL_FIRE_slave_m_bready,
       WILL_FIRE_slave_m_rready,
       WILL_FIRE_slave_m_wvalid,
       WILL_FIRE_trace_data_out_get;

  // remaining internal signals
  wire [63 : 0] stval___1__h1524, x__h1519, y_avValue_fst__h1430;
  wire slave_xactor_f_wr_data_i_notEmpty_AND_master_x_ETC___d8;

  // action method slave_m_awvalid
  assign CAN_FIRE_slave_m_awvalid = 1'd1 ;
  assign WILL_FIRE_slave_m_awvalid = 1'd1 ;

  // value method slave_m_awready
  assign slave_awready = slave_xactor_f_wr_addr$FULL_N ;

  // action method slave_m_wvalid
  assign CAN_FIRE_slave_m_wvalid = 1'd1 ;
  assign WILL_FIRE_slave_m_wvalid = 1'd1 ;

  // value method slave_m_wready
  assign slave_wready = slave_xactor_f_wr_data$FULL_N ;

  // value method slave_m_bvalid
  assign slave_bvalid = slave_xactor_f_wr_resp$EMPTY_N ;

  // value method slave_m_bid
  assign slave_bid = slave_xactor_f_wr_resp$D_OUT[5:2] ;

  // value method slave_m_bresp
  assign slave_bresp = slave_xactor_f_wr_resp$D_OUT[1:0] ;

  // action method slave_m_bready
  assign CAN_FIRE_slave_m_bready = 1'd1 ;
  assign WILL_FIRE_slave_m_bready = 1'd1 ;

  // action method slave_m_arvalid
  assign CAN_FIRE_slave_m_arvalid = 1'd1 ;
  assign WILL_FIRE_slave_m_arvalid = 1'd1 ;

  // value method slave_m_arready
  assign slave_arready = slave_xactor_f_rd_addr$FULL_N ;

  // value method slave_m_rvalid
  assign slave_rvalid = slave_xactor_f_rd_data$EMPTY_N ;

  // value method slave_m_rid
  assign slave_rid = slave_xactor_f_rd_data$D_OUT[70:67] ;

  // value method slave_m_rdata
  assign slave_rdata = slave_xactor_f_rd_data$D_OUT[66:3] ;

  // value method slave_m_rresp
  assign slave_rresp = slave_xactor_f_rd_data$D_OUT[2:1] ;

  // value method slave_m_rlast
  assign slave_rlast = slave_xactor_f_rd_data$D_OUT[0] ;

  // action method slave_m_rready
  assign CAN_FIRE_slave_m_rready = 1'd1 ;
  assign WILL_FIRE_slave_m_rready = 1'd1 ;

  // value method master_m_awvalid
  assign master_awvalid = master_xactor_f_wr_addr$EMPTY_N ;

  // value method master_m_awid
  assign master_awid = master_xactor_f_wr_addr$D_OUT[96:93] ;

  // value method master_m_awaddr
  assign master_awaddr = master_xactor_f_wr_addr$D_OUT[92:29] ;

  // value method master_m_awlen
  assign master_awlen = master_xactor_f_wr_addr$D_OUT[28:21] ;

  // value method master_m_awsize
  assign master_awsize = master_xactor_f_wr_addr$D_OUT[20:18] ;

  // value method master_m_awburst
  assign master_awburst = master_xactor_f_wr_addr$D_OUT[17:16] ;

  // value method master_m_awlock
  assign master_awlock = master_xactor_f_wr_addr$D_OUT[15] ;

  // value method master_m_awcache
  assign master_awcache = master_xactor_f_wr_addr$D_OUT[14:11] ;

  // value method master_m_awprot
  assign master_awprot = master_xactor_f_wr_addr$D_OUT[10:8] ;

  // value method master_m_awqos
  assign master_awqos = master_xactor_f_wr_addr$D_OUT[7:4] ;

  // value method master_m_awregion
  assign master_awregion = master_xactor_f_wr_addr$D_OUT[3:0] ;

  // action method master_m_awready
  assign CAN_FIRE_master_m_awready = 1'd1 ;
  assign WILL_FIRE_master_m_awready = 1'd1 ;

  // value method master_m_wvalid
  assign master_wvalid = master_xactor_f_wr_data$EMPTY_N ;

  // value method master_m_wdata
  assign master_wdata = master_xactor_f_wr_data$D_OUT[72:9] ;

  // value method master_m_wstrb
  assign master_wstrb = master_xactor_f_wr_data$D_OUT[8:1] ;

  // value method master_m_wlast
  assign master_wlast = master_xactor_f_wr_data$D_OUT[0] ;

  // action method master_m_wready
  assign CAN_FIRE_master_m_wready = 1'd1 ;
  assign WILL_FIRE_master_m_wready = 1'd1 ;

  // action method master_m_bvalid
  assign CAN_FIRE_master_m_bvalid = 1'd1 ;
  assign WILL_FIRE_master_m_bvalid = 1'd1 ;

  // value method master_m_bready
  assign master_bready = master_xactor_f_wr_resp$FULL_N ;

  // value method master_m_arvalid
  assign master_arvalid = master_xactor_f_rd_addr$EMPTY_N ;

  // value method master_m_arid
  assign master_arid = master_xactor_f_rd_addr$D_OUT[96:93] ;

  // value method master_m_araddr
  assign master_araddr = master_xactor_f_rd_addr$D_OUT[92:29] ;

  // value method master_m_arlen
  assign master_arlen = master_xactor_f_rd_addr$D_OUT[28:21] ;

  // value method master_m_arsize
  assign master_arsize = master_xactor_f_rd_addr$D_OUT[20:18] ;

  // value method master_m_arburst
  assign master_arburst = master_xactor_f_rd_addr$D_OUT[17:16] ;

  // value method master_m_arlock
  assign master_arlock = master_xactor_f_rd_addr$D_OUT[15] ;

  // value method master_m_arcache
  assign master_arcache = master_xactor_f_rd_addr$D_OUT[14:11] ;

  // value method master_m_arprot
  assign master_arprot = master_xactor_f_rd_addr$D_OUT[10:8] ;

  // value method master_m_arqos
  assign master_arqos = master_xactor_f_rd_addr$D_OUT[7:4] ;

  // value method master_m_arregion
  assign master_arregion = master_xactor_f_rd_addr$D_OUT[3:0] ;

  // action method master_m_arready
  assign CAN_FIRE_master_m_arready = 1'd1 ;
  assign WILL_FIRE_master_m_arready = 1'd1 ;

  // action method master_m_rvalid
  assign CAN_FIRE_master_m_rvalid = 1'd1 ;
  assign WILL_FIRE_master_m_rvalid = 1'd1 ;

  // value method master_m_rready
  assign master_rready = master_xactor_f_rd_data$FULL_N ;

  // actionvalue method trace_data_out_get
  assign trace_data_out_get = f_trace_data$D_OUT ;
  assign RDY_trace_data_out_get = f_trace_data$EMPTY_N ;
  assign CAN_FIRE_trace_data_out_get = f_trace_data$EMPTY_N ;
  assign WILL_FIRE_trace_data_out_get = EN_trace_data_out_get ;

  // submodule f_trace_data
  FIFO2 #(.width(32'd427), .guarded(32'd1)) f_trace_data(.RST(RST_N),
							 .CLK(CLK),
							 .D_IN(f_trace_data$D_IN),
							 .ENQ(f_trace_data$ENQ),
							 .DEQ(f_trace_data$DEQ),
							 .CLR(f_trace_data$CLR),
							 .D_OUT(f_trace_data$D_OUT),
							 .FULL_N(f_trace_data$FULL_N),
							 .EMPTY_N(f_trace_data$EMPTY_N));

  // submodule master_xactor_f_rd_addr
  FIFO2 #(.width(32'd97),
	  .guarded(32'd1)) master_xactor_f_rd_addr(.RST(RST_N),
						   .CLK(CLK),
						   .D_IN(master_xactor_f_rd_addr$D_IN),
						   .ENQ(master_xactor_f_rd_addr$ENQ),
						   .DEQ(master_xactor_f_rd_addr$DEQ),
						   .CLR(master_xactor_f_rd_addr$CLR),
						   .D_OUT(master_xactor_f_rd_addr$D_OUT),
						   .FULL_N(master_xactor_f_rd_addr$FULL_N),
						   .EMPTY_N(master_xactor_f_rd_addr$EMPTY_N));

  // submodule master_xactor_f_rd_data
  FIFO2 #(.width(32'd71),
	  .guarded(32'd1)) master_xactor_f_rd_data(.RST(RST_N),
						   .CLK(CLK),
						   .D_IN(master_xactor_f_rd_data$D_IN),
						   .ENQ(master_xactor_f_rd_data$ENQ),
						   .DEQ(master_xactor_f_rd_data$DEQ),
						   .CLR(master_xactor_f_rd_data$CLR),
						   .D_OUT(master_xactor_f_rd_data$D_OUT),
						   .FULL_N(master_xactor_f_rd_data$FULL_N),
						   .EMPTY_N(master_xactor_f_rd_data$EMPTY_N));

  // submodule master_xactor_f_wr_addr
  FIFO2 #(.width(32'd97),
	  .guarded(32'd1)) master_xactor_f_wr_addr(.RST(RST_N),
						   .CLK(CLK),
						   .D_IN(master_xactor_f_wr_addr$D_IN),
						   .ENQ(master_xactor_f_wr_addr$ENQ),
						   .DEQ(master_xactor_f_wr_addr$DEQ),
						   .CLR(master_xactor_f_wr_addr$CLR),
						   .D_OUT(master_xactor_f_wr_addr$D_OUT),
						   .FULL_N(master_xactor_f_wr_addr$FULL_N),
						   .EMPTY_N(master_xactor_f_wr_addr$EMPTY_N));

  // submodule master_xactor_f_wr_data
  FIFO2 #(.width(32'd73),
	  .guarded(32'd1)) master_xactor_f_wr_data(.RST(RST_N),
						   .CLK(CLK),
						   .D_IN(master_xactor_f_wr_data$D_IN),
						   .ENQ(master_xactor_f_wr_data$ENQ),
						   .DEQ(master_xactor_f_wr_data$DEQ),
						   .CLR(master_xactor_f_wr_data$CLR),
						   .D_OUT(master_xactor_f_wr_data$D_OUT),
						   .FULL_N(master_xactor_f_wr_data$FULL_N),
						   .EMPTY_N(master_xactor_f_wr_data$EMPTY_N));

  // submodule master_xactor_f_wr_resp
  FIFO2 #(.width(32'd6), .guarded(32'd1)) master_xactor_f_wr_resp(.RST(RST_N),
								  .CLK(CLK),
								  .D_IN(master_xactor_f_wr_resp$D_IN),
								  .ENQ(master_xactor_f_wr_resp$ENQ),
								  .DEQ(master_xactor_f_wr_resp$DEQ),
								  .CLR(master_xactor_f_wr_resp$CLR),
								  .D_OUT(master_xactor_f_wr_resp$D_OUT),
								  .FULL_N(master_xactor_f_wr_resp$FULL_N),
								  .EMPTY_N(master_xactor_f_wr_resp$EMPTY_N));

  // submodule slave_xactor_f_rd_addr
  FIFO2 #(.width(32'd97), .guarded(32'd1)) slave_xactor_f_rd_addr(.RST(RST_N),
								  .CLK(CLK),
								  .D_IN(slave_xactor_f_rd_addr$D_IN),
								  .ENQ(slave_xactor_f_rd_addr$ENQ),
								  .DEQ(slave_xactor_f_rd_addr$DEQ),
								  .CLR(slave_xactor_f_rd_addr$CLR),
								  .D_OUT(slave_xactor_f_rd_addr$D_OUT),
								  .FULL_N(slave_xactor_f_rd_addr$FULL_N),
								  .EMPTY_N(slave_xactor_f_rd_addr$EMPTY_N));

  // submodule slave_xactor_f_rd_data
  FIFO2 #(.width(32'd71), .guarded(32'd1)) slave_xactor_f_rd_data(.RST(RST_N),
								  .CLK(CLK),
								  .D_IN(slave_xactor_f_rd_data$D_IN),
								  .ENQ(slave_xactor_f_rd_data$ENQ),
								  .DEQ(slave_xactor_f_rd_data$DEQ),
								  .CLR(slave_xactor_f_rd_data$CLR),
								  .D_OUT(slave_xactor_f_rd_data$D_OUT),
								  .FULL_N(slave_xactor_f_rd_data$FULL_N),
								  .EMPTY_N(slave_xactor_f_rd_data$EMPTY_N));

  // submodule slave_xactor_f_wr_addr
  FIFO2 #(.width(32'd97), .guarded(32'd1)) slave_xactor_f_wr_addr(.RST(RST_N),
								  .CLK(CLK),
								  .D_IN(slave_xactor_f_wr_addr$D_IN),
								  .ENQ(slave_xactor_f_wr_addr$ENQ),
								  .DEQ(slave_xactor_f_wr_addr$DEQ),
								  .CLR(slave_xactor_f_wr_addr$CLR),
								  .D_OUT(slave_xactor_f_wr_addr$D_OUT),
								  .FULL_N(slave_xactor_f_wr_addr$FULL_N),
								  .EMPTY_N(slave_xactor_f_wr_addr$EMPTY_N));

  // submodule slave_xactor_f_wr_data
  FIFO2 #(.width(32'd73), .guarded(32'd1)) slave_xactor_f_wr_data(.RST(RST_N),
								  .CLK(CLK),
								  .D_IN(slave_xactor_f_wr_data$D_IN),
								  .ENQ(slave_xactor_f_wr_data$ENQ),
								  .DEQ(slave_xactor_f_wr_data$DEQ),
								  .CLR(slave_xactor_f_wr_data$CLR),
								  .D_OUT(slave_xactor_f_wr_data$D_OUT),
								  .FULL_N(slave_xactor_f_wr_data$FULL_N),
								  .EMPTY_N(slave_xactor_f_wr_data$EMPTY_N));

  // submodule slave_xactor_f_wr_resp
  FIFO2 #(.width(32'd6), .guarded(32'd1)) slave_xactor_f_wr_resp(.RST(RST_N),
								 .CLK(CLK),
								 .D_IN(slave_xactor_f_wr_resp$D_IN),
								 .ENQ(slave_xactor_f_wr_resp$ENQ),
								 .DEQ(slave_xactor_f_wr_resp$DEQ),
								 .CLR(slave_xactor_f_wr_resp$CLR),
								 .D_OUT(slave_xactor_f_wr_resp$D_OUT),
								 .FULL_N(slave_xactor_f_wr_resp$FULL_N),
								 .EMPTY_N(slave_xactor_f_wr_resp$EMPTY_N));

  // rule RL_write_reqs
  assign CAN_FIRE_RL_write_reqs =
	     slave_xactor_f_wr_addr$EMPTY_N &&
	     slave_xactor_f_wr_data_i_notEmpty_AND_master_x_ETC___d8 ;
  assign WILL_FIRE_RL_write_reqs = CAN_FIRE_RL_write_reqs ;

  // rule RL_rl_connect
  assign CAN_FIRE_RL_rl_connect =
	     master_xactor_f_rd_addr$FULL_N &&
	     slave_xactor_f_rd_addr$EMPTY_N ;
  assign WILL_FIRE_RL_rl_connect = CAN_FIRE_RL_rl_connect ;

  // rule RL_rl_connect_1
  assign CAN_FIRE_RL_rl_connect_1 =
	     slave_xactor_f_wr_resp$FULL_N &&
	     master_xactor_f_wr_resp$EMPTY_N ;
  assign WILL_FIRE_RL_rl_connect_1 = CAN_FIRE_RL_rl_connect_1 ;

  // rule RL_rl_connect_2
  assign CAN_FIRE_RL_rl_connect_2 =
	     slave_xactor_f_rd_data$FULL_N &&
	     master_xactor_f_rd_data$EMPTY_N ;
  assign WILL_FIRE_RL_rl_connect_2 = CAN_FIRE_RL_rl_connect_2 ;

  // submodule f_trace_data
  assign f_trace_data$D_IN =
	     { 171'h12AAAAAAAAAAAAAAA955555554A0000000000000002,
	       x__h1519,
	       slave_xactor_f_wr_addr$D_OUT[92:29],
	       128'hAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA } ;
  assign f_trace_data$ENQ =
	     slave_xactor_f_wr_addr$EMPTY_N &&
	     slave_xactor_f_wr_data_i_notEmpty_AND_master_x_ETC___d8 ;
  assign f_trace_data$DEQ = EN_trace_data_out_get ;
  assign f_trace_data$CLR = 1'b0 ;

  // submodule master_xactor_f_rd_addr
  assign master_xactor_f_rd_addr$D_IN = slave_xactor_f_rd_addr$D_OUT ;
  assign master_xactor_f_rd_addr$ENQ = CAN_FIRE_RL_rl_connect ;
  assign master_xactor_f_rd_addr$DEQ =
	     master_xactor_f_rd_addr$EMPTY_N && master_arready ;
  assign master_xactor_f_rd_addr$CLR = 1'b0 ;

  // submodule master_xactor_f_rd_data
  assign master_xactor_f_rd_data$D_IN =
	     { master_rid, master_rdata, master_rresp, master_rlast } ;
  assign master_xactor_f_rd_data$ENQ =
	     master_rvalid && master_xactor_f_rd_data$FULL_N ;
  assign master_xactor_f_rd_data$DEQ = CAN_FIRE_RL_rl_connect_2 ;
  assign master_xactor_f_rd_data$CLR = 1'b0 ;

  // submodule master_xactor_f_wr_addr
  assign master_xactor_f_wr_addr$D_IN = slave_xactor_f_wr_addr$D_OUT ;
  assign master_xactor_f_wr_addr$ENQ = CAN_FIRE_RL_write_reqs ;
  assign master_xactor_f_wr_addr$DEQ =
	     master_xactor_f_wr_addr$EMPTY_N && master_awready ;
  assign master_xactor_f_wr_addr$CLR = 1'b0 ;

  // submodule master_xactor_f_wr_data
  assign master_xactor_f_wr_data$D_IN = slave_xactor_f_wr_data$D_OUT ;
  assign master_xactor_f_wr_data$ENQ = CAN_FIRE_RL_write_reqs ;
  assign master_xactor_f_wr_data$DEQ =
	     master_xactor_f_wr_data$EMPTY_N && master_wready ;
  assign master_xactor_f_wr_data$CLR = 1'b0 ;

  // submodule master_xactor_f_wr_resp
  assign master_xactor_f_wr_resp$D_IN = { master_bid, master_bresp } ;
  assign master_xactor_f_wr_resp$ENQ =
	     master_bvalid && master_xactor_f_wr_resp$FULL_N ;
  assign master_xactor_f_wr_resp$DEQ = CAN_FIRE_RL_rl_connect_1 ;
  assign master_xactor_f_wr_resp$CLR = 1'b0 ;

  // submodule slave_xactor_f_rd_addr
  assign slave_xactor_f_rd_addr$D_IN =
	     { slave_arid,
	       slave_araddr,
	       slave_arlen,
	       slave_arsize,
	       slave_arburst,
	       slave_arlock,
	       slave_arcache,
	       slave_arprot,
	       slave_arqos,
	       slave_arregion } ;
  assign slave_xactor_f_rd_addr$ENQ =
	     slave_arvalid && slave_xactor_f_rd_addr$FULL_N ;
  assign slave_xactor_f_rd_addr$DEQ = CAN_FIRE_RL_rl_connect ;
  assign slave_xactor_f_rd_addr$CLR = 1'b0 ;

  // submodule slave_xactor_f_rd_data
  assign slave_xactor_f_rd_data$D_IN = master_xactor_f_rd_data$D_OUT ;
  assign slave_xactor_f_rd_data$ENQ = CAN_FIRE_RL_rl_connect_2 ;
  assign slave_xactor_f_rd_data$DEQ =
	     slave_rready && slave_xactor_f_rd_data$EMPTY_N ;
  assign slave_xactor_f_rd_data$CLR = 1'b0 ;

  // submodule slave_xactor_f_wr_addr
  assign slave_xactor_f_wr_addr$D_IN =
	     { slave_awid,
	       slave_awaddr,
	       slave_awlen,
	       slave_awsize,
	       slave_awburst,
	       slave_awlock,
	       slave_awcache,
	       slave_awprot,
	       slave_awqos,
	       slave_awregion } ;
  assign slave_xactor_f_wr_addr$ENQ =
	     slave_awvalid && slave_xactor_f_wr_addr$FULL_N ;
  assign slave_xactor_f_wr_addr$DEQ = CAN_FIRE_RL_write_reqs ;
  assign slave_xactor_f_wr_addr$CLR = 1'b0 ;

  // submodule slave_xactor_f_wr_data
  assign slave_xactor_f_wr_data$D_IN =
	     { slave_wdata, slave_wstrb, slave_wlast } ;
  assign slave_xactor_f_wr_data$ENQ =
	     slave_wvalid && slave_xactor_f_wr_data$FULL_N ;
  assign slave_xactor_f_wr_data$DEQ = CAN_FIRE_RL_write_reqs ;
  assign slave_xactor_f_wr_data$CLR = 1'b0 ;

  // submodule slave_xactor_f_wr_resp
  assign slave_xactor_f_wr_resp$D_IN = master_xactor_f_wr_resp$D_OUT ;
  assign slave_xactor_f_wr_resp$ENQ = CAN_FIRE_RL_rl_connect_1 ;
  assign slave_xactor_f_wr_resp$DEQ =
	     slave_bready && slave_xactor_f_wr_resp$EMPTY_N ;
  assign slave_xactor_f_wr_resp$CLR = 1'b0 ;

  // remaining internal signals
  assign slave_xactor_f_wr_data_i_notEmpty_AND_master_x_ETC___d8 =
	     slave_xactor_f_wr_data$EMPTY_N &&
	     master_xactor_f_wr_addr$FULL_N &&
	     master_xactor_f_wr_data$FULL_N &&
	     f_trace_data$FULL_N ;
  assign stval___1__h1524 = { 32'd0, slave_xactor_f_wr_data$D_OUT[40:9] } ;
  assign x__h1519 =
	     (slave_xactor_f_wr_data$D_OUT[8:1] == 8'h0F) ?
	       stval___1__h1524 :
	       y_avValue_fst__h1430 ;
  assign y_avValue_fst__h1430 =
	     { 32'd0, slave_xactor_f_wr_data$D_OUT[72:41] } ;
endmodule  // mkDM_Mem_Tap

