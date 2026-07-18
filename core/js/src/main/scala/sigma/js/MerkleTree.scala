package sigma.js

import sigma.data.Iso.isoStringToColl
import sigma.data.{CMerkleTree, Iso, MerkleTreeData}

import scala.scalajs.js
import scala.scalajs.js.annotation.JSExportTopLevel

/** Equivalent of [[sigma.MerkleTree]] available from JS. */
@JSExportTopLevel("MerkleTree")
class MerkleTree(val digest: String) extends js.Object

object MerkleTree {

  implicit val isoMerkleTree: Iso[MerkleTree, sigma.MerkleTree] =
    new Iso[MerkleTree, sigma.MerkleTree] {
      override def to(x: MerkleTree): sigma.MerkleTree =
        CMerkleTree(MerkleTreeData(isoStringToColl.to(x.digest)))

      override def from(x: sigma.MerkleTree): MerkleTree =
        new MerkleTree(isoStringToColl.from(x.digest))
    }
}
