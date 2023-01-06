package ethereum.contracts

import ethereum.core.Address
import ethereum.core.Message
import ethereum.core.{Contract, ContractThrowException}
import ethereum.core.Mapping
import ethereum.core.Record
import ethereum.core.Record.{Begin, Commit}

import scala.collection.concurrent.TrieMap

import scala.concurrent.stm._

class EtherDoc(log: Record.Log, _owner:Message) extends Contract(log) {

  val name = this.getClass.getName + Record.counter.addAndGet(1).toString()

  val owner = _owner.getSender()

  val latestDocument : Ref[Int] = Ref(0)

  case class DocumentTransfer(
    blockNumber : Int,
    hash : String,
    from : Address,
    to : Address
  )

  // Data Structures
  val history : Mapping[Int,DocumentTransfer] = new Mapping(this, "history", TrieMap())
  val usedHashes : Mapping[String, Boolean] = new Mapping(this, "usedHashes", TrieMap())
  val documentHashMap : Mapping[String, Address] = new Mapping(this, "documentHashMap", TrieMap())

  // In case you sent funds by accident
  def empty() : Unit = {
     //uint256 balance = address(this).balance;
    //address(owner).send(balance);
  }
    
  def newDocument(msg:Message, hash:String) : Boolean = {
    addToLog(Begin(msg, name, "newDocument("+hash+")"))
    var success = false;
    atomic { implicit txn =>
      if (documentExistsInternal(msg,hash)) { ////// HMM : This is another method
        success = false;
      }else{
        createHistory(msg, hash, msg.sender, msg.sender);
        usedHashes.put(msg, hash, true)
        success = true;
      }
    }
    addToLog(Commit(msg, name, "newDocument"))
    return success;
  }

  // This is "internal"
	def createHistory(msg: Message, hash:String, from:Address, to:Address)(implicit txn:InTxn) : Unit = {
    addToLog(Record.Op(msg, Record.Lock("latestDocument", "get", "latestDocument")))
    addToLog(Record.Op(msg, Record.Lock("latestDocument", "put", "latestDocument")))
		latestDocument.set(latestDocument.get + 1)
		documentHashMap.put(msg, hash, to)
		usedHashes.put(msg, hash, true)
    addToLog(Record.Op(msg, Record.Lock("latestDocument", "get", "latestDocument")))
		history.put(msg, latestDocument.get, DocumentTransfer(msg.tx_id, hash, from, to))
		DocumentEvent(msg.tx_id, hash, from,to)
  }
    
  def transferDocument(msg:Message, hash:String, recipient:Address) : Boolean = {
    addToLog(Begin(msg,name,s"transferDocument(${hash}, ${recipient})"))
    atomic { implicit txn =>
      var success = false;
      if (documentExistsInternal(msg,hash)){
        documentHashMap.get(msg, hash) match {
          case Some(t) =>
            if (t == msg.sender) {
              createHistory(msg, hash, msg.sender, recipient);
              success = true;
            }
          case None => ()
        }
      }
      return success;
    }
    addToLog(Commit(msg,name,s"transferDocument(${hash}, ${recipient})"))
  }

  // internal version
  def documentExistsInternal(msg:Message, hash:String)(implicit txn:InTxn) : Boolean = {
    val rv = usedHashes.get(msg, hash) match {
      case Some(t) => true
      case None => false
    }
    return rv
  }
    
  def documentExists(msg:Message, hash:String) : Boolean = {
    addToLog(Begin(msg,name,s"documentExists(${hash})"))
    val rv = atomic { implicit txn =>
      usedHashes.get(msg, hash) match {
        case Some(t) => true
        case None => false
      }
    }
    addToLog(Commit(msg,name,"documentExists"))
    return rv
  }
    

  // Originally, this function was made to return a tuple so that
  //  the outside didn't need to worry about the Documenttransfer datatype
  // constant returns (uint blockNumber, hash:String, from:Address, to:Address)
  def getDocument(msg:Message, docId:Int) : DocumentTransfer = {
    addToLog(Begin(msg,name,s"getDocument(${docId})"))
    val doc = atomic { implicit txn =>
      history.get(msg, docId) match {
        case Some(d) => d
        case None => throwContract("no such doc")
      }
    }
    addToLog(Commit(msg,name,"getDocument"))
    return doc
  }
    
  def DocumentEvent(blockNumber:Int,hash:String, from:Address, to:Address) : Unit = {
    // println(s"DocumentEvent($blockNumber,$hash,$from,$to)")
  }
  // def getLatest() : Int = {
  //   return latestDocument.get;
  // }
    
}
