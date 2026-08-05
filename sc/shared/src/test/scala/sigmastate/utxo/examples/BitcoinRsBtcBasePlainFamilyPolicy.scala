package sigmastate.utxo.examples

/** Build-time invariants shared by the current Base/PLAIN lifecycle family. */
private[examples] object BitcoinRsBtcBasePlainFamilyPolicy {
  final val ExecutorBounty: Long = 0L
  final val TotalStateDeductionMax: Long = 1000000L

  def requireValidStateDeduction(stateFee: Long): Unit = {
    require(stateFee > 0L, "The state-funded miner fee must be positive")
    require(ExecutorBounty >= 0L, "The executor bounty cannot be negative")
    require(
      stateFee <= TotalStateDeductionMax,
      "The state-funded miner fee exceeds the family deduction cap")
    require(
      ExecutorBounty <= TotalStateDeductionMax - stateFee,
      "The state fee and executor bounty exceed the family deduction cap")
  }
}
