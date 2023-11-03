package ethereum.contracts

import ethereum.core.Address
import ethereum.core.Message
import ethereum.core.{Contract, ContractThrowException}
import ethereum.core.Mapping
import ethereum.core.Record
import ethereum.core.Record._

import scala.collection.concurrent.TrieMap

import scala.concurrent.stm._

/// @title Voting with delegation.
class BallotExpensive(log: Record.Log, msg : Message, proposalNames : List[String]) extends Contract(log) {

  val name = this.getClass.getName + Record.counter.addAndGet(1).toString()

  val chairperson: Address = msg.getSender()

  val pmap = new TrieMap[String, Proposal]
  proposalNames.foreach{ name => pmap.put(name, Proposal(name, 0)) }

  // A dynamically-sized array of `Proposal` structs.
  val proposals: Mapping[String, Proposal] = new Mapping(this, "proposals", pmap)

  // This declares a state variable that
  // stores a `Voter` struct for each possible address.
  //mapping(address => Voter) public voters;
  val voters : Mapping[Address,Voter] =
    new Mapping(this, "voters", TrieMap(chairperson -> Voter(1, false, chairperson, null)))

  // This declares a new complex type which will
  // be used for variables later.
  // It will represent a single voter.
  case class Voter(
    weight : Int, // weight is accumulated by delegation
    voted : Boolean,  // if true, that person already voted
    delegate : Address, // person delegated to
    vote : String   // index of the voted proposal
  )

  // This is a type for a single proposal.
  case class Proposal(
    name : String,   // short name (up to 32 bytes)
    voteCount : Int // number of accumulated votes
  )

  //chairperson = msg.getSender();
  //voters[chairperson].weight = 1;
  // For each of the provided proposal names,
  // create a new proposal object and add it
  // to the end of the array.
  // for (int i = 0; i < proposalNames.length; i++) {
  //     // `Proposal({...})` creates a temporary
  //     // Proposal object and `proposals.push(...)`
  //     // appends it to the end of `proposals`.
  //     proposals.push(Proposal({
  //         name: proposalNames[i],
  //         voteCount: 0
  //     }));
  // }

  // Give `voter` the right to vote on this ballot.
  // May only be called by `chairperson`.
  def giveRightToVote(msg : Message, deleg : Address) : Unit = {
    addToLog(Begin(msg, name, "giveRightToVote(" + msg + ", " + deleg + ")"))
		atomic {
			implicit txn =>
      if (msg.getSender() != chairperson) {
        addToLog(Commit(msg, name, "giveRightToVote", thrown = true))
        throwContract("giveRightToVote");
      }

      voters.get(msg, deleg) match {
        case Some(votr : Voter) =>
          if(votr.voted) {
            addToLog(Commit(msg, name, "giveRightToVote", thrown = true))
            throwContract("giveRightToVote2")
          }
          else {
            voters.put(msg, deleg, votr.copy(weight = 1))
          }
        case None =>
          voters.put(msg, deleg, new Voter(1, false, deleg, null))
      }
    }
    addToLog(Commit(msg, name, "giveRightToVote"))
  }

  def _delegate(msg:Message, to:Address) : Address = {
	  // see if he has deleated to some one else
	  atomic{
		  implicit txn =>
		  voters.get(msg, to) match {
		  case Some(v) =>
		  if (v.delegate != null && v.delegate != msg.getSender()) {
			  _delegate(msg,v.delegate)
		  } else {
			  to
		  }
		  case None =>
		  }
		  // otherwise, done.
		  to
	  }
  }
  
  /// Delegate your vote to the voter `to`.
  def delegate(msg:Message, to : Address) {
	  // assigns reference
	  atomic{
		  implicit txn =>
		  voters.get(msg, msg.getSender()) match {
		  case Some(voter) =>
		  if (voter.voted)
			  throwContract("delegate");

		  // Forward the delegation as long as `to` also delegated.
		  // In general, such loops are very dangerous, because if
		  // they run too long, they might need more gas than is
		  // available in a block.  In this case, the delegation will
		  // not be executed, but in other situations, such loops
		  // might cause a contract to get "stuck" completely.
		  val final_to = _delegate(msg, to)
				  if (final_to == msg.getSender()) { throwContract("delegate2") }

		  voters.put(msg, msg.getSender(), voter.copy(voted = true, delegate = final_to))

		  voters.get(msg, final_to) match {
		  case Some(del) =>
		  if (del.voted) {
			  // If the delegate already voted,
			  // directly add to the number of votes
			  //proposals[del.vote].voteCount = voter.weight + proposals[del.vote].voteCount
			  // TODO
		  } else {
			  // If the delegate did not vote yet,
			  // add to her weight.
			  voters.put(msg, final_to, del.copy(weight = del.weight + voter.weight))
		  }
		  case None =>
		  }
		  case None =>
		  }
	  }

  }

  /// Give your vote (including votes delegated to you)
  /// to proposal `proposals[proposal].name`.
  def vote(msg:Message, prop : String) = {
    addToLog(Begin(msg, name, "vote(" + msg + ", " + prop + ")"))
		atomic {
			implicit txn =>
      voters.get(msg, msg.getSender) match {
        case Some(voter) =>
          if (voter.voted) {
            addToLog(Commit(msg, name, "vote", thrown = true))
            throwContract("already voted");
          }
          // perform some costly computation
          var cnt = 0
          for (i <- 1 to 9999) {
            cnt += 1
          }
          voters.put(msg, msg.getSender, voter.copy(voted = true, vote = prop))

          // If `proposal` is out of the range of the array, this will
          // throw automatically and revert all changes.
          proposals.get(msg, prop) match {
            case Some(proposal) =>
              proposals.put(msg, prop, proposal.copy(voteCount = proposal.voteCount + voter.weight))
            case None =>
              addToLog(Commit(msg, name, "vote", thrown = true))
              throwContract("invalid proposal")
          }
        case None =>
      }
    }
    addToLog(Commit(msg, name, "vote"))
  }

  /// @dev Computes the winning proposal taking all
  /// previous votes into account.
  def winningProposal() /*constant*/ : Proposal = {
	  var winningProposal : Proposal = null;
	  var winningVoteCount : Int = 0;
	  proposalNames.foreach{ name =>
	  atomic {
		  implicit txn =>
		  proposals.get(msg, name) match {
		  case Some(proposal) =>
		  if(proposal.voteCount > winningVoteCount) {
			  winningVoteCount = proposal.voteCount
					  winningProposal = proposal
		  }
		  case None =>
		  // should not happen
		  }
	  }
	
	  }
	  return winningProposal
	  // for (int p = 0; p < proposals.length; p++) {
	  //     if (proposals[p].voteCount > winningVoteCount) {
	  //         winningVoteCount = proposals[p].voteCount;
	  //         winningProposal = p;
	  //     }
	  // }
	  // return winningProposal
  }

  // Calls winningProposal() function to get the index
  // of the winner contained in the proposals array and then
  // returns the name of the winner
  def winnerName() : String = {
    val winnerName = winningProposal().name;
    return winnerName
  }
}
