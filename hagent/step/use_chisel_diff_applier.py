from hagent.tool.chisel_diff_applier import ChiselDiffApplier

# The diff to be applied:
chisel_diff = """@@ -950,7 +950,7 @@
    -  io.result := io.inputx + io.inputy
    +  io.result := io.inputx - io.inputy
"""

# The original Chisel code snippet:
chisel_code = """
// The base abstract CPU module which declares the CoreIO of a CPU
package dinocpu

import chisel3._
import chisel3.util._
import _root_.circt.stage.ChiselStage

/**
  * Base CPU module which all CPU models implement
  */
abstract class BaseCPU extends Module {
  val io = IO(new CoreIO())

  // Required so the compiler doesn't optimize things away when testing
  // incomplete designs.
  dontTouch(io)
}

// This file contains the branch preditor logic

/**
 * I/O for the branch predictors
 *
 * Input:  pc, the pc to use to predict whether the branch is taken or not. From decode
 * Input:  update, true if we should update the prediction we made last cycle
 * Input:  taken, true if the branch was actually taken, false otherwise
 *
 * Output: prediction, true if the branch is predicted to be taken, false otherwise
 */
class BranchPredIO extends Bundle {
  val pc         = Input(UInt(64.W))
  val update     = Input(Bool())
  val taken      = Input(Bool())

  val prediction = Output(Bool())
}

/**
 * Base class for all branch predictors. Simply declares the IO and has some
 * simple functions for updating saturating counters
 */
abstract class BaseBranchPredictor(val c: CPUConfig) extends Module {
  val io = IO(new BranchPredIO)

  // Default value is weakly taken for each branch
  val defaultSaturatingCounter = (1 << c.saturatingCounterBits - 1)
  // Create a register file with c.branchPredTableEntries
  // Each entry is c.saturatingCounterBits.W bits wide
  val predictionTable = RegInit(VecInit(Seq.fill(c.branchPredTableEntries)(defaultSaturatingCounter.U(c.saturatingCounterBits.W))))

  // Function to increment a saturating counter
  def incrCounter(counter: UInt): Unit = {
    val max = (1 << c.saturatingCounterBits) - 1
    when (counter =/= max.U) {
      counter := counter + 1.U
    }
  }

  // Function to decrement a saturating counter
  def decrCounter(counter: UInt): Unit = {
    when (counter =/= 0.U) {
      counter := counter - 1.U
    }
  }
}

/**
 * An always not taken branch predictor
 *
 */
class AlwaysNotTakenPredictor(implicit val conf: CPUConfig) extends BaseBranchPredictor(conf) {
  io.prediction := false.B
}

/**
 * An always taken branch predictor
 *
 */
class AlwaysTakenPredictor(implicit val conf: CPUConfig) extends BaseBranchPredictor(conf) {
  io.prediction := true.B
}

/**
 * A simple local predictor
 */
class LocalPredictor(implicit val conf: CPUConfig) extends BaseBranchPredictor(conf) {

  // Register to store the last branch predicted so we can update the tables.
  // This will also work for back to back branches since we resolve them in
  // execute (one cycle later)
  val lastBranch = Reg(UInt())

  when (io.update) {
    when (io.taken) {
      incrCounter(predictionTable(lastBranch))
    } .otherwise {
      decrCounter(predictionTable(lastBranch))
    }
  }

  // The first bit for the table access is based on the number of entries.
  // +2 since we ignore the bottom two bits
  val tableIndex = io.pc(log2Floor(conf.branchPredTableEntries) + 2, 2)

  // Return the high-order bit
  io.prediction := predictionTable(tableIndex)(conf.saturatingCounterBits - 1)

  // Remember the last pc to update the table later
  lastBranch := tableIndex
}

/**
 * A simple global history predictor
 */
class GlobalHistoryPredictor(implicit val conf: CPUConfig) extends BaseBranchPredictor(conf) {

  // The length is based on the size of the branch history table
  val historyBits = log2Floor(conf.branchPredTableEntries)
  // Need one extra bit for the "last" history
  val history = RegInit(0.U((historyBits+1).W))

  val curhist = history(historyBits,0)
  when(io.update) {
    // Update the prediction for this branch history
    // Use the last branch history.
    when (io.taken) {
      incrCounter(predictionTable(curhist))
    } .otherwise {
      decrCounter(predictionTable(curhist))
    }

    history := Cat(curhist, io.taken) // update the history register at the end of the cycle
  }

  io.prediction := predictionTable(curhist)(conf.saturatingCounterBits - 1)
}

// Configurations for the dinocpu
// For file length
import java.io.File

/**
 * This class configures all of the dinocpus. It takes parameters for the type of CPU model
 * (e.g., single-cycle, five-cycle, etc.), and the memories to hook up.
 */
class CPUConfig
{
  /** The type of CPU to elaborate */
  var cpuType = "single-cycle"

  /** The type of branch predictor to use */
  var branchPredictor = "always-not-taken"
  /** Number of bits for the saturating counters */
  var saturatingCounterBits = 2
  /** Number of entries in the branch predictor table */
  var branchPredTableEntries = 32

  /** The memory file location */
  var memFile = "test"
  /** The noncombinational memory latency */
  var memLatency = 5
  /** The port types **/
  var memPortType = "combinational-port"
  /** The backing memory type */
  var memType = "combinational"

  def printConfig(): Unit = {
    println(s"CPU Type: ${cpuType}")
    println(s"Branch predictor: ${branchPredictor}")
    println(s"Memory file: ${memFile}")
    println(s"Memory type: ${memType}")
    println(s"Memory port type: ${memPortType}")
    println(s"Memory latency (ignored if combinational): ${memLatency}")
  }

  /**
   * Returns the CPU that we will be elaborating
   *
   * @return A CPU to elaborate.
   */
  def getCPU(): BaseCPU = {
    implicit val conf = this
    cpuType match {
      case "single-cycle" => new SingleCycleCPU
      case _ => throw new IllegalArgumentException("Must specify known CPU model")
    }
  }

  def getBranchPredictor: BaseBranchPredictor = {
    implicit val conf = this
    branchPredictor match {
      case "always-taken"     => new AlwaysTakenPredictor
      case "always-not-taken" => new AlwaysNotTakenPredictor
      case "local"            => new LocalPredictor
      case "global"           => new GlobalHistoryPredictor
      case _ => throw new IllegalArgumentException("Must specify known branch predictor")
    }
  }

  /**
    * Create a memory with data from a file
    *
    * @param minSize is the minimum size for the memory. If the binary file is
    *        smaller than this, create a memory that is this size.
    * @return [[BaseDualPortedMemory]] object
    */
  def getNewMem(minSize: Int = 1 << 16): BaseDualPortedMemory = {
    val f = new File(memFile)
    if (f.length == 0) {
      println("WARNING: No file will be loaded for data memory")
    }

    memType match {
      case "combinational"     => new DualPortedCombinMemory (minSize, memFile)
      case "non-combinational" => new DualPortedNonCombinMemory (minSize, memFile, memLatency)
      case _ => throw new IllegalArgumentException("Must specify known backing memory type")
    }
  }

  /**
    * Create an instruction memory port
    *
    * @return [[BaseIMemPort]] object
    */
  def getIMemPort(): BaseIMemPort = {
    val f = new File(memFile)
    if (f.length == 0) {
      println("WARNING: No file will be loaded for data memory")
    }

    memPortType match {
      case "combinational-port"     => new ICombinMemPort
      case "non-combinational-port" => new INonCombinMemPort
      // case "non-combinational-cache" => new ICache
      case _ => throw new IllegalArgumentException("Must specify known instruction memory port type")
    }
  }

  /**
    * Create a data memory port
    *
    * @return [[BaseDMemPort]] object
    */
  def getDMemPort(): BaseDMemPort = {
    val f = new File(memFile)
    if (f.length == 0) {
      println("WARNING: No file will be loaded for data memory")
    }

    memPortType match {
      case "combinational-port"     => new DCombinMemPort
      case "non-combinational-port" => new DNonCombinMemPort
      // case "non-combinational-cache" => new DCache
      case _ => throw new IllegalArgumentException("Must specify known data memory port type")
    }
  }
}
// Main entry point for CPU

class Top(val conf: CPUConfig) extends Module
{
  val io = IO(new Bundle{
    val success = Output(Bool())
  })

  io.success := DontCare

  val cpu  = Module(conf.getCPU())
  val mem  = Module(conf.getNewMem())

  val imem = Module(conf.getIMemPort())
  val dmem = Module(conf.getDMemPort())

  conf.printConfig()

  mem.wireMemory (imem, dmem)
  cpu.io.imem <> imem.io.pipeline
  cpu.io.dmem <> dmem.io.pipeline
}


import chisel3.util.{Decoupled, Valid}
import chisel3.util.experimental.loadMemoryFromFile

/**
  * Base class for all modular backing memories. Simply declares the IO and the memory file.
  */
abstract class BaseDualPortedMemory(size: Int, memfile: String) extends Module {
  def wireMemory (imem: BaseIMemPort, dmem: BaseDMemPort): Unit = {
    // Connect memory imem IO to dmem accessor
    this.io.imem.request <> imem.io.bus.request
    imem.io.bus.response <> this.io.imem.response
    // Connect memory dmem IO to dmem accessor
    this.io.dmem.request <> dmem.io.bus.request
    dmem.io.bus.response <> this.io.dmem.response
  }

  val io = IO(new Bundle {
    val imem = new MemPortBusIO
    val dmem = new MemPortBusIO
  })

  // Intentional DontCares:
  // The connections between the ports and the backing memory, along with the
  // ports internally assigning values to the, means that these DontCares
  // should be completely 'overwritten' when the CPU is elaborated
  io.imem.request <> DontCare
  io.dmem.request <> DontCare
  // Zero out response ports to 0, so that the pipeline does not receive any
  // 'DontCare' values from the memory ports
  io.imem.response <> 0.U.asTypeOf(Valid (new Response))
  io.dmem.response <> 0.U.asTypeOf(Valid (new Response))

  val memory = Mem(math.ceil(size.toDouble/4).toInt, UInt(32.W))
  val memFileObj = new java.io.File(memfile)
  if (memFileObj.exists() && memFileObj.length() > 0) {
    loadMemoryFromFile(memory, memfile)
  } else {
    println(s"WARNING: Memory initialization file '$memfile' not found or empty; skipping loadMemoryFromFile")
  }

}

/**
  * Base class for all instruction ports. Simply declares the IO.
  */
abstract class BaseIMemPort extends Module {
  val io = IO (new Bundle {
    val pipeline = new IMemPortIO
    val bus  = Flipped (new MemPortBusIO)
  })

  io.pipeline <> 0.U.asTypeOf (new IMemPortIO)
  // Intentional DontCare:
  // The connections between the ports and the backing memory, along with the
  // ports internally assigning values to the, means that these DontCares
  // should be completely 'overwritten' when the CPU is elaborated
  io.bus      <> DontCare
}

/**
  * Base class for all data ports. Simply declares the IO.
  */
abstract class BaseDMemPort extends Module {
  val io = IO (new Bundle {
    val pipeline = new DMemPortIO
    val bus = Flipped (new MemPortBusIO)
  })

  io.pipeline <> 0.U.asTypeOf (new DMemPortIO)
  // Intentional DontCare:
  // The connections between the ports and the backing memory, along with the
  // ports internally assigning values to the, means that these DontCares
  // should be completely 'overwritten' when the CPU is elaborated
  io.bus      <> DontCare

  io.pipeline.good := io.bus.response.valid
}

/**
 * The modified asynchronous form of the dual ported memory module.
 * When io.imem.request.valid or io.imem.request.valid is true and the memory is ready for an operation,
 * this memory module simulates the latency of real DRAM by pushing memory accesses into pipes that delay
 * the request for a configurable latency.
 *
 * As with the synced memory module, this memory should only be instantiated in the Top file,
 * and never within the actual CPU.
 *
 * The I/O for this module is defined in [[MemPortBusIO]].
 */
class DualPortedNonCombinMemory(size: Int, memfile: String, latency: Int) extends BaseDualPortedMemory(size, memfile) {
  def wireMemPipe(portio: MemPortBusIO, pipe: Pipe[Request]): Unit = {
    pipe.io.enq.bits      <> DontCare
    pipe.io.enq.valid     := false.B
    portio.response.valid := false.B

    // Memory is technically always ready, but we want to use the
    // ready/valid interface so that if needed we can restrict
    // executing memory operations
    portio.request.ready := true.B
  }
  assert(latency > 0) // Check for attempt to make combinational memory

  // Instruction port
  val imemPipe = Module(new Pipe(new Request, latency))

  wireMemPipe(io.imem, imemPipe)

  when (io.imem.request.valid) {
    // Put the Request into the instruction pipe and signal that instruction memory is busy
    val inRequest = io.imem.request.bits
    imemPipe.io.enq.bits  := inRequest
    imemPipe.io.enq.valid := true.B
  } .otherwise {
    imemPipe.io.enq.valid := false.B
  }

  when (imemPipe.io.deq.valid) {
    // We should only be expecting a read from instruction memory
    assert(imemPipe.io.deq.bits.operation === MemoryOperation.Read)
    val outRequest = imemPipe.io.deq.bits
    // Check that address is pointing to a valid location in memory
    assert (outRequest.address < size.U)
    io.imem.response.valid        := true.B
    io.imem.response.bits.data := Cat(Fill(32, 0.U(1.W)), memory(outRequest.address >> 2)(31, 0))
  } .otherwise {
    // The memory's response can't possibly be valid if the imem pipe isn't outputting a valid request
    io.imem.response.valid := false.B
  }

  // Data port

  val dmemPipe     = Module(new Pipe(new Request, latency))

  wireMemPipe(io.dmem, dmemPipe)

  when (io.dmem.request.valid) {
    // Put the Request into the data pipe and signal that data memory is busy
    val inRequest = io.dmem.request.bits
    dmemPipe.io.enq.bits  := inRequest
    dmemPipe.io.enq.valid := true.B
  } .otherwise {
    dmemPipe.io.enq.valid := false.B
  }

  when (dmemPipe.io.deq.valid) {
    assert (dmemPipe.io.deq.bits.operation =/= MemoryOperation.ReadWrite)
    // Dequeue request and execute
    val outRequest = dmemPipe.io.deq.bits
    val address = outRequest.address >> 2
    // Check that address is pointing to a valid location in memory
    assert (outRequest.address < size.U)

    when (outRequest.operation === MemoryOperation.Read) {
      io.dmem.response.valid        := true.B
      io.dmem.response.bits.data    := Cat(memory(address + 1.U), memory(address))
    } .elsewhen (outRequest.operation === MemoryOperation.Write) {
      io.dmem.response.valid        := false.B
      memory(address) := outRequest.writedata(31, 0)
      memory(address + 1.U) := outRequest.writedata(63, 32)
    }
  } .otherwise {
    // The memory's response can't possibly be valid if the dmem pipe isn't outputting a valid request
    io.dmem.response.valid := false.B
  }
}

// A Bundle used for temporarily storing the necessary information for a  read/write in the data memory accessor.
class OutstandingReq extends Bundle {
  val address   = UInt(64.W)
  val writedata = UInt(64.W)
  val maskmode  = UInt(2.W)
  val operation = MemoryOperation()
  val sext      = Bool()
}

/**
 * The instruction memory port. Since both the combinational and noncombinational instruction ports just issue
 * read requests in the same way both ports have the same implementation
 *
 * The I/O for this module is defined in [[IMemPortIO]].
 */
class INonCombinMemPort extends ICombinMemPort {
  // Non-combinational memory can technically always accept requests since they are delayed through a pipe.
  // But we want to be able to signal that the memory is holding a request, so a register is used to store
  // whether a request passed through this memory port
  val imemBusy = RegInit(false.B)

  io.pipeline.good := io.bus.response.valid

  when (io.pipeline.valid) {
    imemBusy := true.B
  } .elsewhen (io.bus.response.valid) {
    imemBusy := false.B
  }

  io.pipeline.ready := !imemBusy
}

/**
 * The data memory port.
 *
 * The I/O for this module is defined in [[DMemPortIO]].
 */
class DNonCombinMemPort extends BaseDMemPort {

  val dmem_busy = RegInit(false.B)

  // A register to hold intermediate data (e.g., write data, mask mode) while the request
  // is outstanding to memory.
  val outstandingReq = Reg (Valid (new OutstandingReq))
  outstandingReq.valid := false.B

  // Used to set the valid bit of the outstanding request
  val sending = Wire(Bool())

  // When the pipeline is supplying a valid read OR write request, send out the request
  // ... on the condition that there isn't an outstanding request in the queue.
  // We need to process outstanding request first to guarantee atomicity of the memory write operation
  // Ready if either we don't have an outstanding request or the outstanding request is a read and
  // it has been satisfied this cycle. Note: we cannot send a read until one cycle after the write has
  // been sent.
  val ready = !outstandingReq.valid || (io.bus.response.valid && (outstandingReq.valid && outstandingReq.bits.operation === MemoryOperation.Read))
  when (!dmem_busy && io.pipeline.valid && (io.pipeline.memread || io.pipeline.memwrite) && ready) {
    // Check if we aren't issuing both a read and write at the same time
    assert (! (io.pipeline.memread && io.pipeline.memwrite))

    // On either a read or write we must read a whole block from memory. Store the necessary
    // information to redirect the memory's response back into itself through a write
    // operation and get the right subset of the block on a read.
    outstandingReq.bits.address   := io.pipeline.address
    outstandingReq.bits.writedata := io.pipeline.writedata
    outstandingReq.bits.maskmode  := io.pipeline.maskmode
    outstandingReq.bits.sext      := io.pipeline.sext
    when (io.pipeline.memwrite) {
      outstandingReq.bits.operation := MemoryOperation.Write
    } .otherwise {
      outstandingReq.bits.operation := MemoryOperation.Read
    }
    sending := true.B
    dmem_busy := true.B

    // Program memory to perform a read. Always read since we must read before write.
    io.bus.request.bits.address   := io.pipeline.address
    io.bus.request.bits.writedata := 0.U
    io.bus.request.bits.operation := MemoryOperation.Read
    io.bus.request.valid          := true.B
  } .otherwise {
    // no request coming in so don't send a request out
    io.bus.request.valid := false.B
    sending := false.B
    dmem_busy := false.B
  }

  // Response path
  when (io.bus.response.valid) {
    assert(outstandingReq.valid)

    dmem_busy := false.B // No longer processing
    when (outstandingReq.bits.operation === MemoryOperation.Write) {
      val writedata = Wire(UInt(64.W))

      // When not writing a whole double-word
      when (outstandingReq.bits.maskmode =/= 3.U) {
        // Read in the existing piece of data at the address, so we "overwrite" only part of it
        val offset = outstandingReq.bits.address(1, 0)
        val readdata = Wire(UInt(64.W))
        val writedata_mask = Wire(UInt(64.W))
        val writedata_mask_shifted = Wire(UInt(64.W))
        val writedata_shifted = Wire(UInt(64.W))
        val readdata_mask = Wire(UInt(64.W)) // readdata doesn't need to be shifted

        readdata := io.bus.response.bits.data

        when (io.pipeline.maskmode === 0.U) { // Byte
          writedata_mask := Cat(Fill(56, 0.U(1.W)), Fill(8, 1.U(1.W)))
        } .elsewhen (io.pipeline.maskmode === 1.U) { // Half-word
          writedata_mask := Cat(Fill(48, 0.U(1.W)), Fill(16, 1.U(1.W)))
        } .elsewhen (io.pipeline.maskmode === 2.U) { // Word
          writedata_mask := Cat(Fill(32, 0.U(1.W)), Fill(32, 1.U(1.W)))
        } .otherwise { // Double-word
          writedata_mask := Fill(64, 1.U(1.W))
        }

        writedata_mask_shifted := writedata_mask << (offset * 8.U)
        writedata_shifted := outstandingReq.bits.writedata << (offset * 8.U)

        // The read bits and the write bits locations are mutually exclusive
        readdata_mask := ~writedata_mask_shifted

        writedata := (readdata & readdata_mask) | (writedata_shifted & writedata_mask_shifted)
      } .otherwise {
        // Write the entire double-word
        writedata := outstandingReq.bits.writedata
      }

      // Program the memory to issue a write.
      val request = Wire (new Request)
      request.address   := outstandingReq.bits.address
      request.writedata := writedata
      request.operation := MemoryOperation.Write
      io.bus.request.bits  := request
      io.bus.request.valid := true.B
    } .otherwise {
      // Response is valid and we don't have a stored write.
      // Perform masking and sign extension on read data when memory is outputting it
      val readdata_mask      = Wire(UInt(64.W))
      val readdata_mask_sext = Wire(UInt(64.W))

      val offset = outstandingReq.bits.address(1, 0)
      when (outstandingReq.bits.maskmode === 0.U) {
        // Byte
        readdata_mask := (io.bus.response.bits.data >> (offset * 8.U)) & 0xff.U
      } .elsewhen (outstandingReq.bits.maskmode === 1.U) {
        // Half-word
        readdata_mask := (io.bus.response.bits.data >> (offset * 8.U)) & 0xffff.U
      } .elsewhen (outstandingReq.bits.maskmode === 2.U) {
        // Word
        readdata_mask := (io.bus.response.bits.data >> (offset * 8.U)) & 0xffffffffL.U
      } .otherwise {
        // Double-word
        readdata_mask := io.bus.response.bits.data
      }

      when (outstandingReq.bits.sext) {
        when (outstandingReq.bits.maskmode === 0.U) {
          // Byte sign extension
          readdata_mask_sext := Cat(Fill(56, readdata_mask(7)),  readdata_mask(7, 0))
        } .elsewhen (outstandingReq.bits.maskmode === 1.U) {
          // Half-word sign extension
          readdata_mask_sext := Cat(Fill(48, readdata_mask(15)), readdata_mask(15, 0))
        } .elsewhen (outstandingReq.bits.maskmode === 2.U) {
          // Word sign extension
          readdata_mask_sext := Cat(Fill(32, readdata_mask(31)), readdata_mask(31, 0))
        } .otherwise {
          // Double-word sign extension (does nothing)
          readdata_mask_sext := readdata_mask
        }
      } .otherwise {
        readdata_mask_sext := readdata_mask
      }

      io.pipeline.readdata := readdata_mask_sext
    }
    // Mark the outstanding request register as being invalid, unless sending
    outstandingReq.valid := sending
  } .otherwise {
    // Keep the outstanding request valid or invalid unless sending
    outstandingReq.valid := outstandingReq.valid | sending
  }
}



/**
  * The instruction memory port.
  *
  * The I/O for this module is defined in [[IMemPortIO]].
  */
class ICombinMemPort extends BaseIMemPort {
  // When the pipeline is supplying a high valid signal
  when (io.pipeline.valid) {
    val request = Wire(new Request)
    request.address   := io.pipeline.address
    request.operation := MemoryOperation.Read
    request.writedata := 0.U

    io.bus.request.bits  := request
    io.bus.request.valid := true.B
  } .otherwise {
    io.bus.request.valid := false.B
  }

  // Combinational memory is always ready
  io.pipeline.ready := true.B

  // When the memory is outputting a valid instruction
  io.pipeline.good := true.B
  io.pipeline.instruction := io.bus.response.bits.data
}

/**
  * The data memory port.
  *
  * The I/O for this module is defined in [[DMemPortIO]].
  */
class DCombinMemPort extends BaseDMemPort {
  io.pipeline.good := true.B

  when (io.pipeline.valid && (io.pipeline.memread || io.pipeline.memwrite)) {
    // Check that we are not issuing a read and write at the same time
    assert(!(io.pipeline.memread && io.pipeline.memwrite))

    io.bus.request.bits.address := io.pipeline.address
    io.bus.request.valid := true.B

    when (io.pipeline.memwrite) {
      // We issue a ReadWrite to the backing memory.
      // Basic run-down of the ReadWrite operation:
      // - DCombinMemPort sends a ReadWrite at a specific address, **addr**.
      // - Backing memory outputs the data at **addr** in io.response
      // - DCombinMemPort notes that io.memwrite is high in the response path. io.response.bits.data
      //   is masked and sign extended, and sent down io.request.writedata
      // - Backing memory receives the modified writedata and feeds it into the memory at **addr**.
      // Since this is combinational logic, this should theoretically all resolve in one clock cycle with no issues
      io.bus.request.bits.operation := MemoryOperation.ReadWrite
    } .otherwise {
      // Issue a normal read to the backing memory
      io.bus.request.bits.operation := MemoryOperation.Read
    }
  } .otherwise {
    // no request coming in so don't send a request out
    io.bus.request.valid := false.B
  }

  // Response path
  when (io.bus.response.valid) {
    when (io.pipeline.memwrite) {
      // Perform writedata modification and send it down io.request.writedata.
      val writedata = Wire (UInt (64.W))

      // When not writing a whole doubleword
      when (io.pipeline.maskmode =/= 3.U) {
        // Read in the existing piece of data at the address, so we "overwrite" only part of it
        val offset = io.pipeline.address(1, 0)
        val readdata = Wire(UInt(64.W))
        val writedata_mask = Wire(UInt(64.W))
        val writedata_mask_shifted = Wire(UInt(64.W))
        val writedata_shifted = Wire(UInt(64.W))
        val readdata_mask = Wire(UInt(64.W)) // readdata doesn't need to be shifted

        readdata := io.bus.response.bits.data

        when (io.pipeline.maskmode === 0.U) { // Byte
          writedata_mask := Cat(Fill(56, 0.U(1.W)), Fill(8, 1.U(1.W)))
        } .elsewhen (io.pipeline.maskmode === 1.U) { // Half-word
          writedata_mask := Cat(Fill(48, 0.U(1.W)), Fill(16, 1.U(1.W)))
        } .elsewhen (io.pipeline.maskmode === 2.U) { // Word
          writedata_mask := Cat(Fill(32, 0.U(1.W)), Fill(32, 1.U(1.W)))
        } .otherwise { // Double-word
          writedata_mask := Fill(64, 1.U(1.W))
        }

        writedata_mask_shifted := writedata_mask << (offset * 8.U)
        writedata_shifted := io.pipeline.writedata << (offset * 8.U)

        // The read bits and the write bits locations are mutually exclusive
        readdata_mask := ~writedata_mask_shifted

        writedata := (readdata & readdata_mask) | (writedata_shifted & writedata_mask_shifted)
      } .otherwise {
        writedata := io.pipeline.writedata
      }

      io.bus.request.bits.writedata := writedata
    } .elsewhen (io.pipeline.memread) {
      // Perform normal masking and sign extension on the read data
      val readdata_mask      = Wire(UInt(64.W))
      val readdata_mask_sext = Wire(UInt(64.W))

      val offset = io.pipeline.address(1, 0)
      when (io.pipeline.maskmode === 0.U) {
        // Byte
        readdata_mask := (io.bus.response.bits.data >> (offset * 8.U)) & 0xff.U
      } .elsewhen (io.pipeline.maskmode === 1.U) {
        // Half-word
        readdata_mask := (io.bus.response.bits.data >> (offset * 8.U)) & 0xffff.U
      } .elsewhen (io.pipeline.maskmode === 2.U) {
        // Word
        readdata_mask := (io.bus.response.bits.data >> (offset * 8.U)) & 0xffffffffL.U
      } .otherwise {
        // Double-word
        readdata_mask := io.bus.response.bits.data
      }

      when (io.pipeline.sext) {
        when (io.pipeline.maskmode === 0.U) {
          // Byte sign extension
          readdata_mask_sext := Cat(Fill(56, readdata_mask(7)),  readdata_mask(7, 0))
        } .elsewhen (io.pipeline.maskmode === 1.U) {
          // Half-word sign extension
          readdata_mask_sext := Cat(Fill(48, readdata_mask(15)), readdata_mask(15, 0))
        } .elsewhen (io.pipeline.maskmode === 2.U) {
          // Word sign extension
          readdata_mask_sext := Cat(Fill(32, readdata_mask(31)), readdata_mask(31, 0))
        } .otherwise {
          // Double-word sign extension (does nothing)
          readdata_mask_sext := readdata_mask
        }
      } .otherwise {
        readdata_mask_sext := readdata_mask
      }

      io.pipeline.readdata := readdata_mask_sext
    }
  }
}

/**
 * A generic ready/valid interface for MemPort modules, whose IOs extend this.
 *
 * This interface corresponds with the pipeline <=> port interface between the
 * pipelined CPU and the memory port.
 *
 * Input:  address, the address of a piece of data in memory.
 * Input:  valid, true when the address specified is valid
 * Output: good, true when memory is responding with a piece of data (used to un-stall the pipeline)
 *
 */
class MemPortIO extends Bundle {
  // Pipeline <=> Port
  val address  = Input(UInt(64.W))
  val valid    = Input(Bool())
  val good     = Output(Bool())
}

/**
 * The *interface* of the IMemPort module.
 *
 * Pipeline <=> Port:
 *   Input:  address, the address of an instruction in memory
 *   Input:  valid, true when the address specified is valid
 *   Output: instruction, the requested instruction
 *   Output: good, true when memory is responding with a piece of data
 *   Output: ready, true when the memory is ready to accept another request (used to un-stall the pipeline)
 */
class IMemPortIO extends MemPortIO {
  val instruction = Output(UInt(64.W))
  val ready       = Output(Bool())
}

/**
 * The *interface* of the DMemPort module.
 *
 * Pipeline <=> Port:
 *   Input:  address, the address of a piece of data in memory.
 *   Input:  writedata, valid interface for the data to write to the address
 *   Input:  valid, true when the address (and writedata during a write) specified is valid
 *   Input:  memread, true if we are reading from memory
 *   Input:  memwrite, true if we are writing to memory
 *   Input:  maskmode, mode to mask the result. 0 means byte, 1 means halfword, 2 means word, 3 means doubleword
 *   Input:  sext, true if we should sign extend the result
 *   Output: readdata, the data read and sign extended
 *   Output: good, true when memory is responding with a piece of data
 */
class DMemPortIO extends MemPortIO {
  // Pipeline <=> Port
  val writedata = Input(UInt(64.W))
  val memread   = Input(Bool())
  val memwrite  = Input(Bool())
  val maskmode  = Input(UInt(2.W))
  val sext      = Input(Bool())

  val readdata  = Output(UInt(64.W))
}

// A Bundle used for representing a memory access by instruction memory or data memory.
class Request extends Bundle {
  val address      = UInt(64.W)
  val writedata    = UInt(64.W)
  val operation    = MemoryOperation()
}

// A bundle used for representing the memory's response to a memory read operation, which
// is sent back to the issuing memory port.
class Response extends Bundle {
  // The 8-byte-wide block of data being returned by memory
  val data         = UInt(64.W)
}

/**
 * The generic interface for communication between the IMem/DMemPort modules and the backing memory.
 * This interface corresponds with the port <=> memory interface between the
 * memory port and the backing memory.
 *
 * Input:  request, the ready/valid interface for a MemPort module to issue Requests to. Memory
 *         will only accept a request when both request.valid (the MemPort is supplying valid data)
 *         and request.ready (the memory is idling for a request) are high.
 *
 * Output: response, the valid interface for the data outputted by memory if it was requested to read.
 *         the bits in response.bits should only be treated as valid data when response.valid is high.
 */
class MemPortBusIO extends Bundle {
  val request  = Flipped(Decoupled (new Request))
  val response = Valid (new Response)
}
/**
 * A 32 entry two read port one write port register file.
 *
 * Note: this register file *has* an entry for register 0, and it's possible to
 * overwrite the default 0 value. Thus, you need to add extra logic to the
 * DINO CPU control or data path to make sure you always get 0 from register 0.
 *
 * Note: The chisel registers cannot be read and written on the same cycle.
 * Therefore, we have a bypass logic for when a register is read in the same
 * cycle it is written. However, for the single cycle CPU this causes a
 * combinational loop. Thus, we must have different logic when creating a
 * single cycle vs pipelined CPU.
 *
 * Basic operation:
 *   readdata1 = R[readreg1]
 *   readdata2 = R[readreg2]
 *   if (wen) R[writereg] = writedata
 *
 * Input:  readreg1, the number of the register to read
 * Input:  readreg2, the number of the register to read
 * Input:  writereg, the number of the register to write
 * Input:  writedata, the data to write into R[writereg]
 * Input:  wen, write enable. If true, write the writereg register
 *
 * Output: readdata1, the data in register number readreg1 (R[readreg1])
 * Output: readdata2, the data in register number readreg2 (R[readreg2])
 *
 * For more information, see section 4.3 of Patterson and Hennessy
 */
class RegisterFile(implicit val conf: CPUConfig) extends Module {
  val io = IO(new Bundle {
    val readreg1  = Input(UInt(5.W))
    val readreg2  = Input(UInt(5.W))
    val writereg  = Input(UInt(5.W))
    val writedata = Input(UInt(64.W))
    val wen       = Input(Bool())

    val readdata1 = Output(UInt(64.W))
    val readdata2 = Output(UInt(64.W))
  })

  // Required so the compiler doesn't optimize things away when testing
  // incomplete designs.
  dontTouch(io)

  val regs = Reg(Vec(32, UInt(64.W)))

  // When the write enable is high, write the data
  when (io.wen) {
    regs(io.writereg) := io.writedata
  }

  // *Always* read the data. This is required for the single cycle CPU since in a single cycle it
  // might both read and write the registers (e.g., an add)
  io.readdata1 := regs(io.readreg1)
  io.readdata2 := regs(io.readreg2)

  if (conf.cpuType != "single-cycle") {
    // For the five-cycle and pipelined CPU forward the data through the register file
    when (io.readreg1 === io.writereg && io.wen) {
      io.readdata1 := io.writedata
    }
    when (io.readreg2 === io.writereg && io.wen) {
      io.readdata2 := io.writedata
    }
  }
}

/**
 * A simple adder which takes two inputs and returns the sum
 *
 * Input:  inputx the first input operand
 * Input:  inputy the second input operand
 * Output: result first + second
 */
class Adder extends Module {
  val io = IO(new Bundle{
    val inputx    = Input(UInt(64.W))
    val inputy    = Input(UInt(64.W))

    val result    = Output(UInt(64.W))
  })

  io.result := io.inputx + io.inputy
}

/**
 * Takes a RISC-V instruction and returns the sign-exteneded immediate value
 * Note that different RISC-V instruction types have different bits used as the immediate.
 * Also,for the B type and j-type instruction the values are *already* shifted left on the
 * output.
 *
 * Input:  instruction the input full encoded RISC-V instruction
 * Output: sextImm the output sign-extended immediate value encoded in the instruction
 */
class ImmediateGenerator extends Module {
  val io = IO(new Bundle{
    val instruction = Input(UInt(64.W))

    val sextImm     = Output(UInt(64.W))
  })

  io.sextImm := 0.U

  val opcode = io.instruction(6,0)

  switch(opcode) {
    is("b0110111".U) { // U-type (lui)
      // RV64I lui
      // imm = cat(sign_extended_bits, imm[31:12], padding 0s)
      //           (32 bits)           (20 bits)   (12 bits)
      val imm = io.instruction(31, 12)
      io.sextImm := Cat(Fill(32, imm(19)), imm, Fill(12, 0.U))
    }
    is("b0010111".U) { // U-type (auipc)
      // RV64I auipc
      // imm = cat(sign_extended_bits, imm[31:12], padding 0s)
      //           (32 bits)           (20 bits)   (12 bits)
      val imm = io.instruction(31, 12)
      io.sextImm := Cat(Fill(32, imm(19)), imm, Fill(12, 0.U))
    }
    is("b1101111".U) { // J-type (jal)
      // riscv-spec: JAL encodes the offset as a multiple of 2 bytes
      // imm = sign_extends(2 * offset)
      val imm = Cat(io.instruction(31), io.instruction(19,12),
                    io.instruction(20), io.instruction(30,21))
      io.sextImm := Cat(Fill(43, imm(19)), imm, 0.U)
    }
    is("b1100111".U) { // I-type (jalr)
      val imm = io.instruction(31, 20)
      io.sextImm := Cat(Fill(52,imm(11)), imm)
    }
    is("b1100011".U) { // B-type
      val imm = Cat(io.instruction(31), io.instruction(7),
                    io.instruction(30,25), io.instruction(11,8))
      io.sextImm := Cat(Fill(51, imm(11)), imm, 0.U)
    }
    is("b0000011".U) { // I-type (ld)
      val imm = io.instruction(31, 20)
      io.sextImm := Cat(Fill(52, imm(11)), imm)
    }
    is("b0100011".U) { // S-type (st)
      val imm = Cat(io.instruction(31, 25), io.instruction(11,7))
      io.sextImm := Cat(Fill(52, imm(11)), imm)
    }
    is("b0010011".U) { // I-type (immediate arith.) 32-bit
      val imm = io.instruction(31, 20)
      io.sextImm := Cat(Fill(52,imm(11)), imm) // for instructions using shift amount, this imm is also valid as only the lower 5 bits (24, 20) are used
    }
    is("b0011011".U) { // I-type (immediate arith.)
      val imm = io.instruction(31, 20)
      io.sextImm := Cat(Fill(52,imm(11)), imm) // for instructions using shift amount, this imm is also valid as only the lower 6 bits (25, 20) are used
    }
    is("b1110011".U) { // zimm for csri
      io.sextImm := Cat(Fill(59,0.U), io.instruction(19,15))
    }
  }
}

import chisel3.ChiselEnum
object MemoryOperation extends ChiselEnum {
  val Read, Write, ReadWrite = Value
}
// This file is where all of the CPU components are assembled into the whole CPU

/**
 * The main CPU definition that hooks up all of the other components.
 *
 * For more information, see section 4.4 of Patterson and Hennessy
 * This follows figure 4.21
 */
class SingleCycleCPU(implicit val conf: CPUConfig) extends BaseCPU {
  // All of the structures required
  val pc         = dontTouch(RegInit(0.U(64.W)))
  val control    = Module(new Control())
  val registers  = Module(new RegisterFile())
  val aluControl = Module(new ALUControl())
  val alu        = Module(new ALU())
  val immGen     = Module(new ImmediateGenerator())
  val nextpc     = Module(new NextPC())
  val (cycleCount, _) = Counter(true.B, 1 << 30)

  //FETCH
  io.imem.address := pc
  io.imem.valid := true.B

  val instruction = Wire(UInt(32.W))
  when ((pc % 8.U) === 4.U) {
    instruction := io.imem.instruction(63, 32)
  } .otherwise {
    instruction := io.imem.instruction(31, 0)
  }
  val funct3 = instruction(14, 12)

  control.io.opcode := instruction(6, 0)

  registers.io.readreg1 := instruction(19, 15)
  registers.io.readreg2 := instruction(24, 20)
  registers.io.writereg := instruction(11, 7)
  registers.io.writedata := Mux(control.io.toreg, io.dmem.readdata, Mux(control.io.resultselect, immGen.io.sextImm, alu.io.result))
  when (registers.io.writereg =/= 0.U && control.io.regwrite) {
    registers.io.wen := true.B
  } .otherwise {
    registers.io.wen := false.B
  }

  immGen.io.instruction := instruction

  nextpc.io.branch := control.io.branch
  nextpc.io.jumptype := control.io.jumptype
  nextpc.io.inputx := registers.io.readdata1
  nextpc.io.inputy := alu.io.inputy
  nextpc.io.funct3 := funct3
  nextpc.io.pc := pc
  nextpc.io.imm := immGen.io.sextImm

  aluControl.io.aluop := control.io.aluop
  aluControl.io.itype := control.io.itype
  aluControl.io.funct7 := instruction(31, 25)
  aluControl.io.funct3 := instruction(14, 12)
  aluControl.io.wordinst := control.io.wordinst

  alu.io.operation := aluControl.io.operation
  alu.io.inputx := Mux(control.io.src1, pc, registers.io.readdata1)
  alu.io.inputy := MuxCase(0.U, Seq((control.io.src2 === 0.U) -> registers.io.readdata2,
                                      (control.io.src2 === 1.U) -> immGen.io.sextImm,
                                      (control.io.src2 === 2.U) -> 4.U))

  io.dmem.address := alu.io.result
  io.dmem.memread := ~control.io.memop(0)
  io.dmem.memwrite := control.io.memop(0)
  io.dmem.valid := control.io.memop(1)
  io.dmem.maskmode := funct3(1, 0)
  io.dmem.sext := ~funct3(2)
  io.dmem.writedata := registers.io.readdata2

  pc := nextpc.io.nextpc
}

/*
 * Object to make it easier to print information about the CPU
 */
object SingleCycleCPUInfo {
  def getModules(): List[String] = {
    List(
      "dmem",
      "imem",
      "control",
      "registers",
      "csr",
      "aluControl",
      "alu",
      "immGen",
      "nextpc"
    )
  }
}
// The IO between the core and the rest of the system

class CoreIO extends Bundle {
  val imem = Flipped(new IMemPortIO)
  val dmem = Flipped(new DMemPortIO)
}

// Control logic for the processor
import chisel3.util.{BitPat, ListLookup}

/**
 * Main control logic for our simple processor
 *
 * Input: opcode:        Opcode from instruction
 *
 * Output: itype         True if we're working on an itype instruction, False otherwise
 * Output: aluop         True if inst is of R-type or I-type, False otherwise
 * Output: src1          Source for the first ALU/nextpc input (0 if source is readdata1, 1 if source is pc)
 * Output: src2          Source for the second ALU/nextpc input (00 if source is readdata2, 01 if source is immediate, 10 if source is a hardwired value 4 (i.e., alu's inputy = 4))
 * Output: branch        True if branch, False otherwise
 * Output: jumptype      00 if not a jump inst, 10 if inst is jal, 11 is inst is jalr
 * Output: resultselect  0 for result from alu, 1 for immediate
 * Output: memop         00 if not using memory, 10 if reading, and 11 if writing
 * Output: toreg         0 for result from execute, 1 for data from memory
 * Output: regwrite      True if writing to the register file, False otherwise
 * Output: validinst     True if the instruction we're decoding is valid, False otherwise
 * Output: wordinst      True if the instruction *only* operates on 32-bit operands, False otherwise
 *
 * For more information, see section 4.4 of Patterson and Hennessy.
 * This follows figure 4.22.
 */

class Control extends Module {
  val io = IO(new Bundle {
    val opcode = Input(UInt(7.W))

    val itype        = Output(Bool())
    val aluop        = Output(Bool())
    val src1         = Output(Bool())
    val src2         = Output(UInt(2.W))
    val branch       = Output(Bool())
    val jumptype     = Output(UInt(2.W))
    val resultselect = Output(Bool())
    val memop        = Output(UInt(2.W))
    val toreg        = Output(Bool())
    val regwrite     = Output(Bool())
    val validinst    = Output(Bool())
    val wordinst     = Output(Bool())
  })

  val signals =
    ListLookup(io.opcode,
      /*default*/           List(false.B, false.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,  false.B,   false.B,  false.B),
      Array(              /*       itype,   aluop,    src1, src2,   branch,  jumptype, resultselect, memop,   toreg, regwrite, validinst, wordinst */
      // R-format
      BitPat("b0110011") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,  false.B),
      // I-format
      BitPat("b0010011") -> List( true.B,  true.B, false.B,  1.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,  false.B),
      // load
      BitPat("b0000011") -> List(false.B, false.B, false.B,  1.U,  false.B,       0.U,      false.B,   2.U,  true.B,   true.B,    true.B,  false.B),
      // store
      BitPat("b0100011") -> List(false.B, false.B, false.B,  1.U,  false.B,       0.U,      false.B,   3.U, false.B,  false.B,    true.B,  false.B),
      // branch
      BitPat("b1100011") -> List(false.B, false.B, false.B,  0.U,   true.B,       0.U,      false.B,   0.U, false.B,  false.B,    true.B,  false.B),
      // lui
      BitPat("b0110111") -> List(false.B, false.B, false.B,  0.U,  false.B,       0.U,       true.B,   0.U, false.B,   true.B,    true.B,  false.B),
      // auipc
      BitPat("b0010111") -> List(false.B, false.B,  true.B,  1.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,  false.B),
      // jal
      BitPat("b1101111") -> List(false.B, false.B,  true.B,  2.U,  false.B,       2.U,      false.B,   0.U, false.B,   true.B,    true.B,  false.B),
      // jalr
      BitPat("b1100111") -> List(false.B, false.B,  true.B,  2.U,  false.B,       3.U,      false.B,   0.U, false.B,   true.B,    true.B,  false.B),
      // I-format 32-bit operands
      BitPat("b0011011") -> List( true.B,  true.B, false.B,  1.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
      // R-format 32-bit operands
      BitPat("b0111011") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
      ) // Array
    ) // ListLookup

  io.itype        := signals(0)
  io.aluop        := signals(1)
  io.src1         := signals(2)
  io.src2         := signals(3)
  io.branch       := signals(4)
  io.jumptype     := signals(5)
  io.resultselect := signals(6)
  io.memop        := signals(7)
  io.toreg        := signals(8)
  io.regwrite     := signals(9)
  io.validinst    := signals(10)
  io.wordinst     := signals(11)
}

/**
 * The ALU
 *
 * Input:  operation, specifies which operation the ALU should perform
 * Input:  inputx, the first input (e.g., reg1)
 * Input:  inputy, the second input (e.g., reg2)
 * Output: the result of the computation
 */
class ALU extends Module {
  val io = IO(new Bundle {
    val operation = Input(UInt(5.W))
    val inputx    = Input(UInt(64.W))
    val inputy    = Input(UInt(64.W))

    val result    = Output(UInt(64.W))
  })

  val wordinst = Mux(io.operation(4) === 1.U, true.B, false.B)
  val aluop = io.operation(3, 0)

  // this function casts the input to 32-bit UInt, then sign extends it
  val signExtend32To64 = (input: UInt) => Cat(Fill(32, input(31)), input(31, 0))
  val operand1_32 = io.inputx(31, 0)
  val operand2_32 = io.inputy(31, 0)

  when (aluop === "b0110".U) { // and
    io.result := io.inputx & io.inputy
  }
  .elsewhen (aluop === "b0101".U) { // or
    io.result := io.inputx | io.inputy
  }
  .elsewhen (aluop === "b0111".U) { // add
    when (wordinst === true.B) {
      io.result := signExtend32To64(operand1_32 + operand2_32) // + results in width of max(width(op1), width(op2))
    } .otherwise {
      io.result := io.inputx + io.inputy
    }
  }
  .elsewhen (aluop === "b0100".U) { // sub
    when (wordinst === true.B) {
      io.result := signExtend32To64(operand1_32 - operand2_32)
    } .otherwise {
      io.result := io.inputx - io.inputy
    }
  }
  .elsewhen (aluop === "b0011".U) { // sra*
    when (wordinst === true.B) { // sraw
      io.result := signExtend32To64((operand1_32.asSInt >> operand2_32(4, 0)).asUInt) // arithmetic (signed)
                                                                                      // sraw takes 5 bits of op2
    } .otherwise { // sra
      io.result := (io.inputx.asSInt >> io.inputy(5, 0)).asUInt // sra takes 6 bits of op2
    }
  }
  .elsewhen (aluop === "b0001".U) { // sltu
    io.result := (io.inputx < io.inputy)
  }
  .elsewhen (aluop === "b0000".U) { // xor
    io.result := io.inputx ^ io.inputy
  }
  .elsewhen (aluop === "b0010".U) { // srl*
    when (wordinst === true.B) { // srlw
      io.result := signExtend32To64(operand1_32 >> operand2_32(4, 0)) // srlw takes 5 bits of op2
    } .otherwise {
      io.result := io.inputx >> io.inputy(5, 0) // srl takes 6 bits of op2
    }
  }
  .elsewhen (aluop === "b1001".U) { // slt
    io.result := (io.inputx.asSInt < io.inputy.asSInt).asUInt // signed
  }
  .elsewhen (aluop === "b1000".U) { // sll*
    when (wordinst === true.B) { // sllw
      io.result := signExtend32To64(operand1_32 << operand2_32(4, 0)) // sllw takes 5 bits of op2
    } .otherwise {
      io.result := io.inputx << io.inputy(5, 0) // sll takes 6 bits of op2
    }
  }
  .elsewhen (aluop === "b1010".U) { // nor
    io.result := ~(io.inputx | io.inputy)
  }
  .elsewhen (aluop === "b1011".U) { // sge (set greater than or equal)
    io.result := (io.inputx.asSInt >= io.inputy.asSInt).asUInt
  }
  .elsewhen (aluop === "b1100".U) { // sgeu (set greater than or equal unsigned)
    io.result := (io.inputx >= io.inputy)
  }
  .elsewhen (aluop === "b1101".U) { // seq (set equal)
    io.result := io.inputx === io.inputy
  }
  .elsewhen (aluop === "b1110".U) { // sne (set not equal)
    io.result := io.inputx =/= io.inputy
  }
  .otherwise {
    io.result := 0.U // should be invalid
  }
}

// This file contains ALU control logic.
/**
 * The ALU control unit
 *
 * Input:  aluop        0 for ld/st, 1 for R-type
 * Input:  itype        True if I-type
 * Input:  funct7       The most significant bits of the instruction
 * Input:  funct3       The middle three bits of the instruction (12-14)
 * Input:  wordinst     True if the instruction *only* operates on 32-bit operands, False otherwise
 * Output: operation    What we want the ALU to do.
 *
 * For more information, see Section 4.4 and A.5 of Patterson and Hennessy.
 * This is loosely based on figure 4.12
 */
class ALUControl extends Module {
  val io = IO(new Bundle {
    val aluop     = Input(Bool())
    val itype     = Input(Bool())
    val funct7    = Input(UInt(7.W))
    val funct3    = Input(UInt(3.W))
    val wordinst  = Input(Bool())

    val operation = Output(UInt(5.W))
  })

  when (io.aluop === 0.U) {
    io.operation := "b00111".U // add
  } .otherwise {
    when (io.funct3 === "b000".U) {
      when (io.itype | io.funct7 === "b0000000".U) {
        when (io.wordinst) {
          io.operation := "b10111".U // addw
        } .otherwise {
          io.operation := "b00111".U // add
        }
      } .elsewhen (io.funct7 === "b0100000".U) {
                when (io.wordinst) {
          io.operation := "b10100".U // subw
        } .otherwise {
          io.operation := "b00100".U // sub
        }
      } .otherwise {
        io.operation := "b11111".U // invalid operation
      }
    } .elsewhen (io.funct3 === "b001".U) {
      when (io.wordinst) {
        io.operation := "b11000".U // sllw
      } .otherwise {
        io.operation := "b01000".U // sll
      }
    } .elsewhen (io.funct3 === "b010".U) {
      io.operation := "b01001".U // slt
    } .elsewhen (io.funct3 === "b011".U) {
      io.operation := "b00001".U // sltu
    } .elsewhen (io.funct3 === "b100".U) {
      io.operation := "b00000".U // xor
    } .elsewhen (io.funct3 === "b101".U) {
      when (io.funct7(6,1) === "b000000".U) {
        when (io.wordinst) {
          io.operation := "b10010".U // srlw
        } .otherwise {
          io.operation := "b00010".U // srl
        }
      } .elsewhen (io.funct7(6,1) === "b010000".U) {
        when (io.wordinst) {
          io.operation := "b10011".U // sraw
        } .otherwise {
          io.operation := "b00011".U // sra
        }
      } .otherwise {
        io.operation := "b11111".U // invalid operation
      }
    } .elsewhen (io.funct3 === "b110".U) {
      io.operation := "b00101".U // or
    } .otherwise { // b111
      io.operation := "b00110".U // and
    }
  }
}

// Logic to calculate the next pc

/**
 * Next PC unit. This takes various inputs and outputs the next address of the next instruction.
 *
 * Input: branch         True if executing a branch instruction, False otherwise
 * Input: jumptype       00 if not a jump inst, 10 if inst is a jal, 11 if inst is a jalr
 * Input: inputx         First input
 * Input: inputy         Second input
 * Input: funct3         The funct3 from the instruction
 * Input: pc             The *current* program counter for this instruction
 * Input: imm            The sign-extended immediate
 *
 * Output: nextpc        The address of the next instruction
 * Output: taken         True if the next pc is not pc+4
 *
 */
class NextPC extends Module {
  val io = IO(new Bundle {
    val branch   = Input(Bool())
    val jumptype = Input(UInt(2.W))
    val inputx   = Input(UInt(64.W))
    val inputy   = Input(UInt(64.W))
    val funct3   = Input(UInt(3.W))
    val pc       = Input(UInt(64.W))
    val imm      = Input(UInt(64.W))

    val nextpc   = Output(UInt(64.W))
    val taken    = Output(Bool())
  })

  when (io.branch) {
    when ( (io.funct3 === "b000".U & io.inputx === io.inputy)
         | (io.funct3 === "b001".U & io.inputx =/= io.inputy)
         | (io.funct3 === "b100".U & io.inputx.asSInt < io.inputy.asSInt)
         | (io.funct3 === "b101".U & io.inputx.asSInt >= io.inputy.asSInt)
         | (io.funct3 === "b110".U & io.inputx < io.inputy)
         | (io.funct3 === "b111".U & io.inputx >= io.inputy)) {
      io.nextpc := io.pc + io.imm
      io.taken := true.B
    }
    .otherwise {
      io.nextpc := io.pc + 4.U
      io.taken := false.B
    }
  } .elsewhen (io.jumptype =/= 0.U) {
    io.nextpc := Mux(io.jumptype(0), io.inputx + io.imm, // jalr
                                     io.pc + io.imm)     // jal
    io.taken := true.B
  } .otherwise {
    io.nextpc := io.pc + 4.U
    io.taken := false.B
  }

}
// The instruction and data memory modules

/**
  * This is the actual memory. You should never directly use this in the CPU.
  * This module should only be instantiated in the Top file.
  *
  * The I/O for this module is defined in [[MemPortBusIO]].
  */

class DualPortedCombinMemory(size: Int, memfile: String) extends BaseDualPortedMemory (size, memfile) {
  def wireMemPipe(portio: MemPortBusIO): Unit = {
    portio.response.valid := false.B
    // Combinational memory is inherently always ready for port requests
    portio.request.ready := true.B
  }

  // Instruction port

  wireMemPipe(io.imem)

  when (io.imem.request.valid) {
    // Put the Request into the instruction pipe and signal that instruction memory is busy
    val request = io.imem.request.bits

    // We should only be expecting a read from instruction memory
    assert(request.operation === MemoryOperation.Read)
    // Check that address is pointing to a valid location in memory

    // TODO: Revert this back to the assert form "assert (request.address < size.U)"
    // TODO: once CSR is integrated into CPU
    when (request.address < size.U) {
      io.imem.response.valid := true.B
      val baseAddress = (request.address >> 3.U) << 1.U
      io.imem.response.bits.data := Cat(memory(baseAddress + 1.U), memory(baseAddress))
    } .otherwise {
      io.imem.response.valid := false.B
    }
  } .otherwise {
    io.imem.response.valid := false.B
  }

  // Data port

  wireMemPipe(io.dmem)

  val memAddress = io.dmem.request.bits.address
  val memWriteData = io.dmem.request.bits.writedata

  when (io.dmem.request.valid) {
    val request = io.dmem.request.bits

    // Check that non-combin write isn't being used
    assert (request.operation =/= MemoryOperation.Write)
    // Check that address is pointing to a valid location in memory
    assert (request.address < size.U)

    // Read path
    val baseAddress = memAddress >> 2.U
    io.dmem.response.bits.data := Cat(memory(baseAddress + 1.U), memory(baseAddress))
    io.dmem.response.valid := true.B

    // Write path
    when (request.operation === MemoryOperation.ReadWrite) {
      memory(memAddress >> 2) := memWriteData(31, 0)
      memory((memAddress >> 2) + 1.U) := memWriteData(63, 32)
    }
  } .otherwise {
    io.dmem.response.valid := false.B
  }
}

object Main extends App {
  ChiselStage.emitSystemVerilogFile(
    new Top(new CPUConfig),
    firtoolOpts = Array("-disable-all-randomization","--lowering-options=disallowPackedArrays,disallowLocalVariables")
  )
}
"""
applier = ChiselDiffApplier()
new_code = applier.apply_diff(chisel_diff, chisel_code)
print(new_code)