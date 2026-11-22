package gezi.egraph

import gezi.ir.BindingNormalForm
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Instruction

/** The front end's spelling of a thunk layer with holes, a function of its
  * code, holes and number of fillings alone
  * (`BindingNormalForm.respelled`): the layer itself (`Canonical`), or a
  * code, holes and fillings that are closed terms over the placeholders of
  * the fillings (`Respelled`). A subterm a code kept inline that reads no
  * binder, which a β residual leaves once the arguments fill the binders it
  * read, becomes a filling.
  */
enum Respelling:
  case Canonical
  case Respelled(code: Code, holes: Vector[Hole], fillings: Vector[Instruction])

object Respelling:

  /** The key of a thunk layer's spelling in the memo (`EGraph.respellings`). */
  final case class Key(code: Code, holes: Vector[Hole], fillingCount: Int)

  /** The spelling of the thunk of the key. Throws as
    * `BindingNormalForm.respelled` does.
    */
  def of(key: Key): Respelling =
    BindingNormalForm.respelled(key.code, key.holes, key.fillingCount) match
      case None                          => Canonical
      case Some((code, holes, fillings)) => Respelled(code, holes, fillings)

/** The respelling memo's readings (`EGraph.respellings`): the spellings
  * computed, the spellings read back from the memo, and the thunk layers
  * whose spelling differed from the layer.
  */
final case class RespellingCounts(spellingsComputed: Int, spellingsRead: Long, layersRespelled: Long):
  def withComputed: RespellingCounts = copy(spellingsComputed = spellingsComputed + 1)
  def withRead: RespellingCounts = copy(spellingsRead = spellingsRead + 1)
  def withRespelled: RespellingCounts = copy(layersRespelled = layersRespelled + 1)
