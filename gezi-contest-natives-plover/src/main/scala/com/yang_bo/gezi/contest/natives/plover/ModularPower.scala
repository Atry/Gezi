package com.yang_bo.gezi.contest.natives.plover

import java.math.BigInteger

/** A natural to the power of a natural modulo a positive modulus, with the
  * power of zero being one, the value of the definition it replaces, the typed
  * version `plover_typed_modular_power`, in O(log exponent) modular
  * multiplications.
  *
  * The base and the exponent are canonical naturals and the modulus is
  * positive, which is what the native's places declare. A native does not check
  * its operands (`CONTRIBUTING.md`, "Types live only in the term").
  */
object ModularPower:

  /** base^exponent modulo the modulus. */
  def power(
      base: BigInteger,
      exponent: BigInteger,
      modulus: BigInteger
  ): BigInteger =
    base.modPow(exponent, modulus)
