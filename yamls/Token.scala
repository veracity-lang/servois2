package ethereum.contracts

import ethereum.core.Address
import ethereum.core.Message
import ethereum.core.{Contract, ContractThrowException}
import ethereum.core.Mapping
import ethereum.core.Record
import ethereum.core.Record._

import scala.collection.concurrent.TrieMap

import scala.concurrent.stm._

/// @title An ERC token contract based on https://raw.githubusercontent.com/OpenZeppelin/zeppelin-solidity/master/contracts/token/StandardToken.sol
class Token(log: Record.Log, msg : Message, initialTokens: Int) extends Contract(log) {

  val name = this.getClass.getName + Record.counter.addAndGet(1).toString()

  val owner: Address = msg.getSender()

  // This stores account balances.
  val balances: Mapping[Address, Int] =
    new Mapping(this, "balances", TrieMap(owner -> initialTokens))

  // This stores token transfer allowances.
  val allowed: Mapping[Address, Mapping[Address, Int]] = new Mapping(this, "allowed", TrieMap())

  def transfer(msg: Message, to: Address, value: Int) : Boolean = {
    addToLog(Begin(msg, name, "transfer(" + msg + ", " + to + ", " + value + ")"))
		atomic {
			implicit txn =>
      // require(_to != address(0));
      if (! (to != Address("0"))) {
        addToLog(Commit(msg, name, "transfer"))
        throwContract("transfer")
      }

      balances.get(msg, msg.getSender()) match {
        case Some(from_balance: Int) =>

          // require(_value <= balances[msg.sender]);
          if (! (value <= from_balance)) {
            addToLog(Commit(msg, name, "transfer"))
            throwContract("transfer")
          }

          // balances[msg.sender] = balances[msg.sender].sub(_value);
          balances.put(msg, msg.getSender(), from_balance - value)

          // balances[_to] = balances[_to].add(_value);
          val to_balance = balances.get(msg, to) match {
            case Some(balance: Int) =>
              balance
            case None =>
              0
          }
          balances.put(msg, to, to_balance + value)

        case None =>
          addToLog(Commit(msg, name, "transfer"))
          throwContract("transfer")
      }

      // event Transfer(msg.sender, _to, _value);
    }
    addToLog(Commit(msg, name, "transfer"))
    true
  }

  // Transfer some amount from one account to another, if there is
  // enough in allowed.
  def transferFrom(msg: Message, from: Address, to: Address, value: Int) : Boolean = {
    addToLog(Begin(msg, name, "transferFrom(" + msg + ", " + from + ", " + to + ", " + value + ")"))
		atomic {
			implicit txn =>

      // require(_to != address(0));
      if (! (to != Address("0"))) {
        addToLog(Commit(msg, name, "transferFrom"))
        throwContract("transferFrom")
      }

      balances.get(msg, from) match {
        case Some(from_balance: Int) =>

          // require(_value <= balances[_from]);
          if (! (value <= from_balance)) {
            addToLog(Commit(msg, name, "transferFrom"))
            throwContract("transferFrom")
          }

          allowed.get(from) match {
            case Some(from_allowed: Mapping[Address, Int]) =>
              from_allowed.get(msg, to) match {
                case Some(allowed_by_from: Int) =>

                  // require(_value <= allowed[_from][msg.sender]);
                  if (! (value <= allowed_by_from)) {
                    addToLog(Commit(msg, name, "transferFrom"))
                    throwContract("transferFrom")
                  }

                  // balances[_from] = balances[_from].sub(_value);
                  balances.put(msg, from, from_balance - value)

                  val to_balance = balances.get(msg, to) match {
                    case Some(balance: Int) =>
                      balance
                    case None =>
                      balances.put(msg, to, 0)
                      0
                  }

                  // balances[_to] = balances[_to].add(_value);
                  balances.put(msg, to, to_balance + value)

                  // allowed[_from][msg.sender] = allowed[_from][msg.sender].sub(_value);
                  from_allowed.put(msg, from, allowed_by_from - value)

                  // event Transfer(_from, _to, _value);
                case None =>
                  addToLog(Commit(msg, name, "transferFrom"))
                  throwContract("transferFrom")
              }
            case None =>
              addToLog(Commit(msg, name, "transferFrom"))
              throwContract("transferFrom")
          }
        case None =>
          addToLog(Commit(msg, name, "transferFrom"))
          throwContract("transferFrom")
      }
    }
    addToLog(Commit(msg, name, "transferFrom"))
    true
  }

  def approve(msg: Message, spender: Address, value: Int) : Boolean = {
    addToLog(Begin(msg, name, "approve(" + msg + ", " + spender + ", " + value + ")"))
		atomic {
			implicit txn =>

      val from_allowed = allowed.get(msg.getSender()) match {
        case Some(from_allowed: Mapping[Address, Int]) =>
          from_allowed
        case None =>
          val mapping = new Mapping[Address, Int](this, msg.getSender().addr, TrieMap())
          allowed.put(msg, msg.getSender(), mapping)
          mapping
      }

      // allowed[msg.sender][_spender] = _value;
      from_allowed.put(msg, spender, value)

      // event Approval(msg.sender, _spender, _value);
    }
    addToLog(Commit(msg, name, "approve"))
    true
  }

  def allowance(msg: Message, owner: Address, spender: Address) : Int = {
		atomic {
			implicit txn =>
      //return allowed[_owner][_spender];
      allowed.get(owner) match {
        case Some(from_allowed: Mapping[Address, Int]) =>
          from_allowed.get(msg, spender) match {
            case Some(amount: Int) =>
              amount
            case None =>
              0
          }
        case None =>
          0
      }
    }
  }

  def increaseApproval(msg: Message, spender: Address, addedValue: Int) : Boolean = {
    addToLog(Begin(msg, name, "increaseApproval(" + msg + ", " + spender + ", " + addedValue + ")"))
		atomic {
			implicit txn =>

      val from_allowed = allowed.get(msg.getSender()) match {
        case Some(from_allowed: Mapping[Address, Int]) =>
          from_allowed
        case None =>
          val mapping = new Mapping[Address, Int](this, msg.getSender().addr, TrieMap())
          allowed.put(msg.getSender(), mapping)
          mapping
      }

      // allowed[msg.sender][_spender] = allowed[msg.sender][_spender].add(_addedValue);
      val previousAmount = from_allowed.get(msg, spender) match {
        case Some(amount: Int) =>
          amount
        case None =>
          0
      }

      from_allowed.put(msg, spender, previousAmount + addedValue)

      // event Approval(msg.sender, _spender, allowed[msg.sender][_spender]);
    }
    addToLog(Commit(msg, name, "increaseApproval"))
    true
  }
}
