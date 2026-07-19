package sigma.stark.circuit

/** The v3_0 succinct verifier-context parameters, parsed from
  * `stark-kats/circuit_params.tsv` (schema in `circuit_tables.md`; oracles:
  * risc0-circuit-recursion 4.0.4 `control_id.rs`/`info.rs`, risc0-zkp 3.0.4
  * `lib.rs`/`adapter.rs`).
  *
  * `params` keeps every `param` row verbatim; the typed vals below are the
  * ones the verifier consumes, validated at parse. `controlIds` are the
  * `ALLOWED_CONTROL_IDS` in leaf order of the Poseidon2 Merkle tree whose
  * root is [[allowedControlRoot]]; `namedControlIds` are the informational
  * `POSEIDON2_CONTROL_IDS` (name → hex).
  */
final class CircuitParams(
    val params: Map[String, String],
    val controlIds: IndexedSeq[String],
    val namedControlIds: IndexedSeq[(String, String)],
    val proofSystemInfo: String,
    val circuitInfo: String,
    val outputSize: Int,
    val mixSize: Int,
    val queries: Int,
    val invRate: Int,
    val extSize: Int,
    val checkSize: Int,
    val friFold: Int,
    val friFoldPo2: Int,
    val friMinDegree: Int,
    val minCyclesPo2: Int,
    val maxCyclesPo2: Int,
    val minLiftPo2: Int,
    val hashfn: String,
    val allowedControlRoot: String
)

object CircuitParams {

  private val Hex32 = "^[0-9a-f]{64}$"

  /** Parse `circuit_params.tsv` content. Total: malformed input yields
    * `Left`, never throws. Validates presence and shape of every typed
    * parameter, the control-id count, and hex32 formatting of all digests.
    */
  def parse(lines: Iterator[String]): Either[String, CircuitParams] =
    try parseChecked(lines)
    catch {
      case e: NumberFormatException => Left(s"circuit_params: bad number: ${e.getMessage}")
    }

  private def parseChecked(lines: Iterator[String]): Either[String, CircuitParams] = {
    val params = scala.collection.mutable.LinkedHashMap.empty[String, String]
    val controlIds = scala.collection.mutable.ArrayBuffer.empty[String]
    val namedControlIds = scala.collection.mutable.ArrayBuffer.empty[(String, String)]

    while (lines.hasNext) {
      val line = lines.next()
      if (line.nonEmpty && !line.startsWith("#")) {
        val f = line.split("\t", -1)
        f(0) match {
          case "param" =>
            if (f.length != 3) return Left(s"circuit_params: bad param row: $line")
            params.put(f(1), f(2))
          case "control_id" =>
            if (f.length != 3) return Left(s"circuit_params: bad control_id row: $line")
            val idx = f(1).toInt
            if (idx != controlIds.length)
              return Left(s"circuit_params: control_id index $idx out of order (expected ${controlIds.length})")
            if (!f(2).matches(Hex32))
              return Left(s"circuit_params: control_id $idx not hex32: ${f(2)}")
            controlIds += f(2)
          case "named_control_id" =>
            if (f.length != 3) return Left(s"circuit_params: bad named_control_id row: $line")
            if (!f(2).matches(Hex32))
              return Left(s"circuit_params: named_control_id ${f(1)} not hex32: ${f(2)}")
            namedControlIds += ((f(1), f(2)))
          case other => return Left(s"circuit_params: unknown row kind '$other'")
        }
      }
    }

    def str(key: String): String = params.get(key) match {
      case Some(v) => v
      case None    => throw new NumberFormatException(s"missing param '$key'")
    }
    def int(key: String): Int = str(key).toInt

    val root = str("allowed_control_root")
    if (!root.matches(Hex32))
      return Left(s"circuit_params: allowed_control_root not hex32: $root")
    val idCount = int("allowed_control_ids_count")
    if (controlIds.length != idCount)
      return Left(s"circuit_params: ${controlIds.length} control ids but allowed_control_ids_count=$idCount")

    Right(new CircuitParams(
      params = params.toMap,
      controlIds = controlIds.toIndexedSeq,
      namedControlIds = namedControlIds.toIndexedSeq,
      proofSystemInfo = str("proof_system_info"),
      circuitInfo = str("circuit_info"),
      outputSize = int("output_size"),
      mixSize = int("mix_size"),
      queries = int("queries"),
      invRate = int("inv_rate"),
      extSize = int("ext_size"),
      checkSize = int("check_size"),
      friFold = int("fri_fold"),
      friFoldPo2 = int("fri_fold_po2"),
      friMinDegree = int("fri_min_degree"),
      minCyclesPo2 = int("min_cycles_po2"),
      maxCyclesPo2 = int("max_cycles_po2"),
      minLiftPo2 = int("min_lift_po2"),
      hashfn = str("hashfn"),
      allowedControlRoot = root
    ))
  }
}
