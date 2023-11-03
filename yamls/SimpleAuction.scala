
package ethereum.contracts

import ethereum.core.Address
import ethereum.core.Message
import ethereum.core.{Contract, ContractThrowException}
import ethereum.core.Mapping
import ethereum.core.Record
import ethereum.core.Record.{Begin, Commit}

import scala.collection.concurrent.TrieMap

import scala.concurrent.stm._
import scala.concurrent.stm.{Ref}

class SimpleAuction(log: Record.Log, _biddingTime:Long, _beneficiary:Message) extends Contract(log) {

    val name = this.getClass.getName + Record.counter.addAndGet(1).toString()
    def now() : Long = { System.currentTimeMillis / 1000 }

    // Parameters of the auction. Times are either
    // absolute unix timestamps (seconds since 1970-01-01)
    // or time periods in seconds.
    val beneficiary  : Address = _beneficiary.getSender()
    val auctionStart : Long = now()
    val biddingTime  : Long = _biddingTime

    // Current state of the auction.
    val highestBidder : Ref[Address] = Ref(null)
    val highestBid : Ref[Int] = Ref(0)
    //val x:Ref[Int] = Ref((new Int)())

    // Allowed withdrawals of previous bids
  val pendingReturns : Mapping[Address,Int] = new Mapping(this, "pendingReturns", TrieMap[Address,Int]())

    // Set to true at the end, disallows any change
    var ended: Boolean = false

    // Events that will be fired on changes.
    def HighestBidIncreased(bidder : Address, amount : Int) : Unit = {
      // println(f"HighestBidIncreased to $amount%d")
    }

  def AuctionEnded(winner : Address, amount : Int) : Unit = {
      // println(f"Auctionended at $amount%d")
    }

    // The following is a so-called natspec comment,
    // recognizable by the three slashes.
    // It will be shown when the user is asked to
    // confirm a transaction.

    /// Create a simple auction with `_biddingTime`
    /// seconds bidding time on behalf of the
    /// beneficiary address `_beneficiary`.
    // def SimpleAuction(
    //     uint _biddingTime,
    //     address _beneficiary
    // ) {
    //     beneficiary = _beneficiary;
    //     auctionStart = now;
    //     biddingTime = _biddingTime;
    // }

  def bidPlusOne(msg: Message) {
    addToLog(Begin(msg, name, "bidPlusOne"))
    atomic {
      implicit txn =>
      addToLog(Record.Op(msg, Record.Lock("highestBid", "get", "highestBid")))
      addToLog(Record.Op(msg, Record.Lock("highestBid", "put", "highestBid")))
      highestBid.set(highestBid.get + 1)
      addToLog(Record.Op(msg, Record.Lock("highestBid", "get", "highestBid")))
      pendingReturns.put(msg, msg.getSender(), highestBid.get + 1)
      addToLog(Record.Op(msg, Record.Lock("highestBidder", "put", "highestBidder")))
      highestBidder.set(msg.getSender())
    }
    addToLog(Commit(msg, name, "bidPlusOne"))
  }

    /// Bid on the auction with the value sent
    /// together with this transaction.
    /// The value will only be refunded if the
    /// auction is not won.
    def bid(msg:Message,msg_value:Int) : Unit = { // payable
      addToLog(Begin(msg, name, "bid"))
      atomic { implicit txn =>
        // No arguments are necessary, all
        // information is already part of
        // the transaction. The keyword payable
        // is required for the function to
        // be able to receive Ether.
        if (now() > auctionStart + biddingTime) {
            // Revert the call if the bidding
            // period is over.
            addToLog(Commit(msg, name, "bid", thrown = true))
            throwContract("bidding over");
        }
        addToLog(Record.Op(msg, Record.Lock("highestBid", "get", "highestBid")))
        if (msg_value <= highestBid.get) {
            // If the bid is not higher, send the
            // money back.
            addToLog(Commit(msg, name, "bid", thrown = true))
            throwContract("not highest");
          println("2")
        }
        addToLog(Record.Op(msg, Record.Lock("highestBidder", "get", "highestBidder")))
        if (highestBidder.get != null) {
            // Sending back the money by simply using
            // highestBidder.send(highestBid) is a security risk
            // because it can be prevented by the caller by e.g.
            // raising the call stack to 1023. It is always safer
            // to let the recipient withdraw their money themselves.
            addToLog(Record.Op(msg, Record.Lock("highestBidder", "get", "highestBidder")))
            val cur : Int = pendingReturns.get(msg, highestBidder.get) match {
              case Some(v) => v
              case None => 0
            }
            addToLog(Record.Op(msg, Record.Lock("highestBidder", "get", "highestBidder")))
            addToLog(Record.Op(msg, Record.Lock("highestBid", "get", "highestBid")))
            pendingReturns.put(msg, highestBidder.get, cur + highestBid.get)
            //pendingReturns[highestBidder] += highestBid;
          println("3")
        }
        println("4")
        addToLog(Record.Op(msg, Record.Lock("highestBidder", "put", "highestBidder")))
        highestBidder.set(msg.getSender())
        addToLog(Record.Op(msg, Record.Lock("highestBid", "set", "highestBid")))
        highestBid.set(msg_value)
        HighestBidIncreased(msg.getSender(), msg_value);
      }
      addToLog(Commit(msg, name, "bid"))
    }

    /// Withdraw a bid that was overbid.
    def withdraw(msg:Message) : Boolean = {
      addToLog(Begin(msg, name, "withdraw"))
      atomic { implicit txn =>
        pendingReturns.get(msg, msg.getSender()) match {
          case Some(amount) =>
            if (amount > 0) {
              // It is important to set this to zero because the recipient
              // can call this function again as part of the receiving call
              // before `send` returns.
              pendingReturns.put(msg, msg.getSender(), 0);

              //if (!msg.getSender().send(amount)) {
                // No need to call throw here, just reset the amount owing
                //pendingReturns.put(msg.getSender(), amount)
                //return false;
              //}
            }
          case None =>
            pendingReturns.put(msg, msg.getSender(), 0);
        }
      }
      addToLog(Commit(msg, name, "withdraw"))
      true
    }

    /// End the auction and send the highest bid
    /// to the beneficiary.
    def auctionEnd(msg: Message) : Unit = { atomic { implicit txn =>
        // It is a good guideline to structure functions that interact
        // with other contracts (i.e. they call functions or send Ether)
        // into three phases:
        // 1. checking conditions
        // 2. performing actions (potentially changing conditions)
        // 3. interacting with other contracts
        // If these phases are mixed up, the other contract could call
        // back into the current contract and modify the state or cause
        // effects (ether payout) to be perfromed multiple times.
        // If functions called internally include interaction with external
        // contracts, they also have to be considered interaction with
        // external contracts.

        // 1. Conditions
        if (now() <= auctionStart + biddingTime)
            throwContract("auction did not yet end")
        if (ended)
            throwContract("this function has already been called")

        // 2. Effects
        ended = true;
        addToLog(Record.Op(msg, Record.Lock("highestBidder", "get", "highestBidder")))
        addToLog(Record.Op(msg, Record.Lock("highestBid", "get", "highestBid")))
        AuctionEnded(highestBidder.get, highestBid.get);

        // 3. Interaction
        //if (!beneficiary.send(highestBid))
        //  throwContract("not beneficiary")
    } }
}
