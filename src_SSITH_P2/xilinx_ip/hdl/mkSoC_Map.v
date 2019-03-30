//
// Generated by Bluespec Compiler, version 2017.07.A (build 4f360250d, 2017-07-21)
//
//
//
//
// Ports:
// Name                         I/O  size props
// m_plic_addr_base               O    64 const
// m_plic_addr_size               O    64 const
// m_plic_addr_lim                O    64 const
// m_near_mem_io_addr_base        O    64 const
// m_near_mem_io_addr_size        O    64 const
// m_near_mem_io_addr_lim         O    64 const
// m_flash_mem_addr_base          O    64 const
// m_flash_mem_addr_size          O    64 const
// m_flash_mem_addr_lim           O    64 const
// m_ethernet_0_addr_base         O    64 const
// m_ethernet_0_addr_size         O    64 const
// m_ethernet_0_addr_lim          O    64 const
// m_dma_0_addr_base              O    64 const
// m_dma_0_addr_size              O    64 const
// m_dma_0_addr_lim               O    64 const
// m_uart16550_0_addr_base        O    64 const
// m_uart16550_0_addr_size        O    64 const
// m_uart16550_0_addr_lim         O    64 const
// m_gpio_0_addr_base             O    64 const
// m_gpio_0_addr_size             O    64 const
// m_gpio_0_addr_lim              O    64 const
// m_boot_rom_addr_base           O    64 const
// m_boot_rom_addr_size           O    64 const
// m_boot_rom_addr_lim            O    64 const
// m_ddr4_0_uncached_addr_base    O    64 const
// m_ddr4_0_uncached_addr_size    O    64 const
// m_ddr4_0_uncached_addr_lim     O    64 const
// m_ddr4_0_cached_addr_base      O    64 const
// m_ddr4_0_cached_addr_size      O    64 const
// m_ddr4_0_cached_addr_lim       O    64 const
// m_is_mem_addr                  O     1
// m_is_IO_addr                   O     1
// m_is_near_mem_IO_addr          O     1
// m_pc_reset_value               O    64 const
// m_mtvec_reset_value            O    64 const
// m_nmivec_reset_value           O    64 const
// CLK                            I     1 unused
// RST_N                          I     1 unused
// m_is_mem_addr_addr             I    64
// m_is_IO_addr_addr              I    64
// m_is_near_mem_IO_addr_addr     I    64
//
// Combinational paths from inputs to outputs:
//   m_is_mem_addr_addr -> m_is_mem_addr
//   m_is_IO_addr_addr -> m_is_IO_addr
//   m_is_near_mem_IO_addr_addr -> m_is_near_mem_IO_addr
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

module mkSoC_Map(CLK,
		 RST_N,

		 m_plic_addr_base,

		 m_plic_addr_size,

		 m_plic_addr_lim,

		 m_near_mem_io_addr_base,

		 m_near_mem_io_addr_size,

		 m_near_mem_io_addr_lim,

		 m_flash_mem_addr_base,

		 m_flash_mem_addr_size,

		 m_flash_mem_addr_lim,

		 m_ethernet_0_addr_base,

		 m_ethernet_0_addr_size,

		 m_ethernet_0_addr_lim,

		 m_dma_0_addr_base,

		 m_dma_0_addr_size,

		 m_dma_0_addr_lim,

		 m_uart16550_0_addr_base,

		 m_uart16550_0_addr_size,

		 m_uart16550_0_addr_lim,

		 m_gpio_0_addr_base,

		 m_gpio_0_addr_size,

		 m_gpio_0_addr_lim,

		 m_boot_rom_addr_base,

		 m_boot_rom_addr_size,

		 m_boot_rom_addr_lim,

		 m_ddr4_0_uncached_addr_base,

		 m_ddr4_0_uncached_addr_size,

		 m_ddr4_0_uncached_addr_lim,

		 m_ddr4_0_cached_addr_base,

		 m_ddr4_0_cached_addr_size,

		 m_ddr4_0_cached_addr_lim,

		 m_is_mem_addr_addr,
		 m_is_mem_addr,

		 m_is_IO_addr_addr,
		 m_is_IO_addr,

		 m_is_near_mem_IO_addr_addr,
		 m_is_near_mem_IO_addr,

		 m_pc_reset_value,

		 m_mtvec_reset_value,

		 m_nmivec_reset_value);
  input  CLK;
  input  RST_N;

  // value method m_plic_addr_base
  output [63 : 0] m_plic_addr_base;

  // value method m_plic_addr_size
  output [63 : 0] m_plic_addr_size;

  // value method m_plic_addr_lim
  output [63 : 0] m_plic_addr_lim;

  // value method m_near_mem_io_addr_base
  output [63 : 0] m_near_mem_io_addr_base;

  // value method m_near_mem_io_addr_size
  output [63 : 0] m_near_mem_io_addr_size;

  // value method m_near_mem_io_addr_lim
  output [63 : 0] m_near_mem_io_addr_lim;

  // value method m_flash_mem_addr_base
  output [63 : 0] m_flash_mem_addr_base;

  // value method m_flash_mem_addr_size
  output [63 : 0] m_flash_mem_addr_size;

  // value method m_flash_mem_addr_lim
  output [63 : 0] m_flash_mem_addr_lim;

  // value method m_ethernet_0_addr_base
  output [63 : 0] m_ethernet_0_addr_base;

  // value method m_ethernet_0_addr_size
  output [63 : 0] m_ethernet_0_addr_size;

  // value method m_ethernet_0_addr_lim
  output [63 : 0] m_ethernet_0_addr_lim;

  // value method m_dma_0_addr_base
  output [63 : 0] m_dma_0_addr_base;

  // value method m_dma_0_addr_size
  output [63 : 0] m_dma_0_addr_size;

  // value method m_dma_0_addr_lim
  output [63 : 0] m_dma_0_addr_lim;

  // value method m_uart16550_0_addr_base
  output [63 : 0] m_uart16550_0_addr_base;

  // value method m_uart16550_0_addr_size
  output [63 : 0] m_uart16550_0_addr_size;

  // value method m_uart16550_0_addr_lim
  output [63 : 0] m_uart16550_0_addr_lim;

  // value method m_gpio_0_addr_base
  output [63 : 0] m_gpio_0_addr_base;

  // value method m_gpio_0_addr_size
  output [63 : 0] m_gpio_0_addr_size;

  // value method m_gpio_0_addr_lim
  output [63 : 0] m_gpio_0_addr_lim;

  // value method m_boot_rom_addr_base
  output [63 : 0] m_boot_rom_addr_base;

  // value method m_boot_rom_addr_size
  output [63 : 0] m_boot_rom_addr_size;

  // value method m_boot_rom_addr_lim
  output [63 : 0] m_boot_rom_addr_lim;

  // value method m_ddr4_0_uncached_addr_base
  output [63 : 0] m_ddr4_0_uncached_addr_base;

  // value method m_ddr4_0_uncached_addr_size
  output [63 : 0] m_ddr4_0_uncached_addr_size;

  // value method m_ddr4_0_uncached_addr_lim
  output [63 : 0] m_ddr4_0_uncached_addr_lim;

  // value method m_ddr4_0_cached_addr_base
  output [63 : 0] m_ddr4_0_cached_addr_base;

  // value method m_ddr4_0_cached_addr_size
  output [63 : 0] m_ddr4_0_cached_addr_size;

  // value method m_ddr4_0_cached_addr_lim
  output [63 : 0] m_ddr4_0_cached_addr_lim;

  // value method m_is_mem_addr
  input  [63 : 0] m_is_mem_addr_addr;
  output m_is_mem_addr;

  // value method m_is_IO_addr
  input  [63 : 0] m_is_IO_addr_addr;
  output m_is_IO_addr;

  // value method m_is_near_mem_IO_addr
  input  [63 : 0] m_is_near_mem_IO_addr_addr;
  output m_is_near_mem_IO_addr;

  // value method m_pc_reset_value
  output [63 : 0] m_pc_reset_value;

  // value method m_mtvec_reset_value
  output [63 : 0] m_mtvec_reset_value;

  // value method m_nmivec_reset_value
  output [63 : 0] m_nmivec_reset_value;

  // signals for module outputs
  wire [63 : 0] m_boot_rom_addr_base,
		m_boot_rom_addr_lim,
		m_boot_rom_addr_size,
		m_ddr4_0_cached_addr_base,
		m_ddr4_0_cached_addr_lim,
		m_ddr4_0_cached_addr_size,
		m_ddr4_0_uncached_addr_base,
		m_ddr4_0_uncached_addr_lim,
		m_ddr4_0_uncached_addr_size,
		m_dma_0_addr_base,
		m_dma_0_addr_lim,
		m_dma_0_addr_size,
		m_ethernet_0_addr_base,
		m_ethernet_0_addr_lim,
		m_ethernet_0_addr_size,
		m_flash_mem_addr_base,
		m_flash_mem_addr_lim,
		m_flash_mem_addr_size,
		m_gpio_0_addr_base,
		m_gpio_0_addr_lim,
		m_gpio_0_addr_size,
		m_mtvec_reset_value,
		m_near_mem_io_addr_base,
		m_near_mem_io_addr_lim,
		m_near_mem_io_addr_size,
		m_nmivec_reset_value,
		m_pc_reset_value,
		m_plic_addr_base,
		m_plic_addr_lim,
		m_plic_addr_size,
		m_uart16550_0_addr_base,
		m_uart16550_0_addr_lim,
		m_uart16550_0_addr_size;
  wire m_is_IO_addr, m_is_mem_addr, m_is_near_mem_IO_addr;

  // remaining internal signals
  wire m_is_IO_addr_addr_ULT_0x70000000___d35;

  // value method m_plic_addr_base
  assign m_plic_addr_base = 64'h000000000C000000 ;

  // value method m_plic_addr_size
  assign m_plic_addr_size = 64'h0000000000400000 ;

  // value method m_plic_addr_lim
  assign m_plic_addr_lim = 64'd205520896 ;

  // value method m_near_mem_io_addr_base
  assign m_near_mem_io_addr_base = 64'h0000000010000000 ;

  // value method m_near_mem_io_addr_size
  assign m_near_mem_io_addr_size = 64'h0000000000010000 ;

  // value method m_near_mem_io_addr_lim
  assign m_near_mem_io_addr_lim = 64'd268500992 ;

  // value method m_flash_mem_addr_base
  assign m_flash_mem_addr_base = 64'h0000000040000000 ;

  // value method m_flash_mem_addr_size
  assign m_flash_mem_addr_size = 64'h0000000000010000 ;

  // value method m_flash_mem_addr_lim
  assign m_flash_mem_addr_lim = 64'd1073807360 ;

  // value method m_ethernet_0_addr_base
  assign m_ethernet_0_addr_base = 64'h0000000062100000 ;

  // value method m_ethernet_0_addr_size
  assign m_ethernet_0_addr_size = 64'h0000000000040000 ;

  // value method m_ethernet_0_addr_lim
  assign m_ethernet_0_addr_lim = 64'd1645477888 ;

  // value method m_dma_0_addr_base
  assign m_dma_0_addr_base = 64'h0000000062200000 ;

  // value method m_dma_0_addr_size
  assign m_dma_0_addr_size = 64'h0000000000010000 ;

  // value method m_dma_0_addr_lim
  assign m_dma_0_addr_lim = 64'd1646329856 ;

  // value method m_uart16550_0_addr_base
  assign m_uart16550_0_addr_base = 64'h0000000062300000 ;

  // value method m_uart16550_0_addr_size
  assign m_uart16550_0_addr_size = 64'h0000000000001000 ;

  // value method m_uart16550_0_addr_lim
  assign m_uart16550_0_addr_lim = 64'd1647316992 ;

  // value method m_gpio_0_addr_base
  assign m_gpio_0_addr_base = 64'h000000006FFF0000 ;

  // value method m_gpio_0_addr_size
  assign m_gpio_0_addr_size = 64'h0000000000010000 ;

  // value method m_gpio_0_addr_lim
  assign m_gpio_0_addr_lim = 64'd1879048192 ;

  // value method m_boot_rom_addr_base
  assign m_boot_rom_addr_base = 64'h0000000070000000 ;

  // value method m_boot_rom_addr_size
  assign m_boot_rom_addr_size = 64'h0000000000001000 ;

  // value method m_boot_rom_addr_lim
  assign m_boot_rom_addr_lim = 64'd1879052288 ;

  // value method m_ddr4_0_uncached_addr_base
  assign m_ddr4_0_uncached_addr_base = 64'h0000000080000000 ;

  // value method m_ddr4_0_uncached_addr_size
  assign m_ddr4_0_uncached_addr_size = 64'h0000000040000000 ;

  // value method m_ddr4_0_uncached_addr_lim
  assign m_ddr4_0_uncached_addr_lim = 64'h00000000C0000000 ;

  // value method m_ddr4_0_cached_addr_base
  assign m_ddr4_0_cached_addr_base = 64'h00000000C0000000 ;

  // value method m_ddr4_0_cached_addr_size
  assign m_ddr4_0_cached_addr_size = 64'h0000000040000000 ;

  // value method m_ddr4_0_cached_addr_lim
  assign m_ddr4_0_cached_addr_lim = 64'h0000000100000000 ;

  // value method m_is_mem_addr
  assign m_is_mem_addr =
	     m_is_mem_addr_addr >= 64'h00000000C0000000 &&
	     m_is_mem_addr_addr < 64'h0000000100000000 ;

  // value method m_is_IO_addr
  assign m_is_IO_addr =
	     m_is_IO_addr_addr >= 64'h000000000C000000 &&
	     m_is_IO_addr_addr < 64'd205520896 ||
	     m_is_IO_addr_addr >= 64'h0000000010000000 &&
	     m_is_IO_addr_addr < 64'd268500992 ||
	     m_is_IO_addr_addr >= 64'h0000000040000000 &&
	     m_is_IO_addr_addr < 64'd1073807360 ||
	     m_is_IO_addr_addr >= 64'h0000000062100000 &&
	     m_is_IO_addr_addr < 64'd1645477888 ||
	     m_is_IO_addr_addr >= 64'h0000000062200000 &&
	     m_is_IO_addr_addr < 64'd1646329856 ||
	     m_is_IO_addr_addr >= 64'h0000000062300000 &&
	     m_is_IO_addr_addr < 64'd1647316992 ||
	     m_is_IO_addr_addr >= 64'h000000006FFF0000 &&
	     m_is_IO_addr_addr_ULT_0x70000000___d35 ||
	     !m_is_IO_addr_addr_ULT_0x70000000___d35 &&
	     m_is_IO_addr_addr < 64'd1879052288 ||
	     m_is_IO_addr_addr >= 64'h0000000080000000 &&
	     m_is_IO_addr_addr < 64'h00000000C0000000 ;

  // value method m_is_near_mem_IO_addr
  assign m_is_near_mem_IO_addr =
	     m_is_near_mem_IO_addr_addr >= 64'h0000000010000000 &&
	     m_is_near_mem_IO_addr_addr < 64'd268500992 ;

  // value method m_pc_reset_value
  assign m_pc_reset_value = 64'h0000000070000000 ;

  // value method m_mtvec_reset_value
  assign m_mtvec_reset_value = 64'h0000000000001000 ;

  // value method m_nmivec_reset_value
  assign m_nmivec_reset_value = 64'hAAAAAAAAAAAAAAAA ;

  // remaining internal signals
  assign m_is_IO_addr_addr_ULT_0x70000000___d35 =
	     m_is_IO_addr_addr < 64'h0000000070000000 ;
endmodule  // mkSoC_Map
