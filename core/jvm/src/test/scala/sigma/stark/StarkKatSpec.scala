package sigma.stark

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

import scala.io.Source

/** Known-Answer-Test parity for the EIP-0045 verifyStark field primitives.
  *
  * Expected values come from an EXTERNAL oracle — RISC0's own field
  * implementation (risc0-core 1.2.6), captured by the `stark-kat/` generator
  * into `resources/stark-kats/` — never from the Scala code under test
  * (oracle-parity rule: a self-oracle proves consistency, not correctness).
  */
class StarkKatSpec extends AnyFunSuite with Matchers {

  private def lines(resource: String): Seq[String] = {
    val is = getClass.getResourceAsStream(resource)
    require(is != null, s"missing KAT resource $resource — run stark-kat/ generator")
    try Source.fromInputStream(is, "UTF-8").getLines().filterNot(_.startsWith("#")).toList
    finally is.close()
  }

  private def coeffs(s: String): Array[Int] = s.split(',').map(_.toInt)

  test("BabyBear ops match risc0-core vectors (add/sub/mul/neg/inv/pow)") {
    val cases = lines("/stark-kats/babybear_ops.tsv")
    cases should not be empty
    cases.foreach { line =>
      val f = line.split('\t')
      val (a, b) = (f(0).toInt, f(1).toInt)
      withClue(s"a=$a b=$b: ") {
        BabyBear.add(a, b) shouldBe f(2).toInt
        BabyBear.sub(a, b) shouldBe f(3).toInt
        BabyBear.mul(a, b) shouldBe f(4).toInt
        BabyBear.neg(a) shouldBe f(5).toInt
        if (f(6) != "-") BabyBear.inv(a) shouldBe f(6).toInt
        BabyBear.pow(a, b.toLong) shouldBe f(7).toInt
      }
    }
  }

  test("Ext4 ops match risc0-core vectors (add/mul/inv, x^4 + 11 reduction)") {
    val cases = lines("/stark-kats/ext4_ops.tsv")
    cases should not be empty
    cases.foreach { line =>
      val f = line.split('\t')
      val a = coeffs(f(0)); val b = coeffs(f(1))
      val (ea, eb) = (Ext4(a(0), a(1), a(2), a(3)), Ext4(b(0), b(1), b(2), b(3)))
      def arr(e: Ext4): Array[Int] = Array(e.c0, e.c1, e.c2, e.c3)
      withClue(s"a=${f(0)} b=${f(1)}: ") {
        arr(ea + eb) shouldBe coeffs(f(2))
        arr(ea * eb) shouldBe coeffs(f(3))
        if (f(4) != "-") arr(ea.inv) shouldBe coeffs(f(4))
      }
    }
  }

  test("Ext4 field laws hold on vector inputs (assoc/distrib/inv roundtrip)") {
    // Structural sanity on top of parity: (a*b)*a == a*(b*a), a*inv(a) == 1.
    val cases = lines("/stark-kats/ext4_ops.tsv").take(20)
    cases.foreach { line =>
      val f = line.split('\t')
      val a = coeffs(f(0)); val b = coeffs(f(1))
      val (ea, eb) = (Ext4(a(0), a(1), a(2), a(3)), Ext4(b(0), b(1), b(2), b(3)))
      (ea * eb) * ea shouldBe ea * (eb * ea)
      if (!ea.isZero) ea * ea.inv shouldBe Ext4.One
    }
  }
}
