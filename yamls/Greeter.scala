package ethereum.contracts

import ethereum.core.Address
import ethereum.core.Message
import ethereum.core.Contract
import ethereum.core.Record

abstract class Mortal(log: Record.Log, msg : Message) extends Contract(log) {
  /* this function is executed at initialization and sets the owner of the contract */
  val owner = msg.getSender()

  /* Function to recover the funds on the contract */
  def kill(msg : Message) = {
    if (msg.getSender() == owner)
      println("mortal selfdestruct.")
  }
}

class Greeter(log: Record.Log, msg : Message, greeting:String) extends Mortal(log, msg) {
  /* define variable greeting of the type string */
  //def this(_msg:Message,_greeting:String) =

  /* this runs when the contract is executed */
  //function greeter(string _greeting) public {
  //greeting = _greeting;
  //}

  /* main function */
  def greet() : String = {
    print ("greet: " + greeting + "\n")
    return greeting
  }
}
