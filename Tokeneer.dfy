class Token{
  
  var fingerprint : int;
  var clearanceLvl : int;
  var valid :bool;
  
  method Init(fingerprint : int, clearance : int)
  modifies this;
  requires fingerprint != 0;
  requires 1 <= clearance <= 3;
  ensures this.fingerprint == fingerprint;
  ensures this.clearanceLvl == clearance;
  ensures valid == true;
  {
    this.fingerprint := fingerprint;
    this.clearanceLvl := clearance;
    this.valid := true;
  }
  
  method invalidate()
  modifies this`valid;
  ensures valid == false;
  {
    valid := false;
  }
  
}

class IdStn{
  var open : bool;
  var securityLvl : int;
  var alarm : bool;
  
  method Init(init_securityLvl : int)
  modifies this;
  requires 1 <= init_securityLvl <=3;  
  ensures securityLvl == init_securityLvl;
  ensures open == false;
  ensures alarm == false;
  {
    securityLvl := init_securityLvl;
    open := false;
    alarm := false;
  }
  
  method Open(user : User, fingerprint : int) returns (access : bool)
  modifies user.token`valid,this`open, this`alarm;
  requires user.token.valid;
  requires user != null && user.token != null;
  ensures open == true;
  ensures !user.token.valid ==> alarm == true;
  {
      if(!user.token.valid)
      {
        user.token.invalidate();
        alarm := true;
      }
      else if(user.token.clearanceLvl >= securityLvl)
      {
        open := true;
      }
      
  }
  
  method Close()
  modifies this`open;
  ensures open == false;
  {
    open := false;
  }


}

class EnrollmentStn{

  var users : set<User>;
  method Init()
  modifies this;
  ensures users == {};
  ensures fresh(users);
  {
    this.users := {};
  }
  
  method Enroll(user: User, fingerprint: int, clearanceLvl : int)
  modifies this,user`token, user.token;
  requires user != null && user.token == null;
  requires clearanceLvl == 1 || clearanceLvl == 2 || clearanceLvl == 3;
  requires user !in users ;
  ensures users == old(users) + {user};
  ensures user.token != null;
  ensures user.token.clearanceLvl == clearanceLvl;
  ensures user.token.fingerprint == fingerprint;
  ensures fresh(user);
  ensures user.token.valid == true;
  {
      user.token := new Token.Init(fingerprint, clearanceLvl);
      users := users + {user};
  }

}

class User{
  var token : Token.init(1,1);
 
 method Init()
  modifies this;
  ensures this.token == null;
  {
    this.token := null;
  }
}

method main(){




}
