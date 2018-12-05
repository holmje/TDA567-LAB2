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
  modifies `valid;
  ensures !valid;
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

  method Open(token : Token, fingerprint : int) returns (access : bool)
  modifies token`valid,this`open, this`alarm;
  requires token.valid;
  requires token != null;
  ensures token.valid && token.clearanceLvl >= securityLvl ==> open == true;
  ensures !token.valid ==> alarm == true;
  {
      if(!token.valid)
      {
        token.invalidate();
        alarm := true;
		access :=false;
      }
      else if(token.clearanceLvl >= securityLvl)
      {
        open := true;
		access :=true;
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
  var users : set<int>;
  var length : int;

  method Init()
  modifies this;
  ensures users == {};
  //ensures fresh(users);
  {
    this.users := {};
    this.length := 0;
  }

  method Enroll(fingerprint: int, clearanceLvl : int) returns (token : Token?)
  modifies this, `length;
  requires clearanceLvl == 1 || clearanceLvl == 2 || clearanceLvl == 3;
  requires fingerprint != 0;
  ensures fingerprint !in users ==> length >= 0;
  ensures fingerprint !in users ==> length >= old(length);
  ensures fingerprint !in users ==> fresh(token);
  ensures fingerprint !in users ==> token.valid == true;
  {
      if (fingerprint in users){
        token := null;
      } else {
        token := new Token.Init(fingerprint, clearanceLvl);
        users := users + {fingerprint};
        length := length + 1;
      }
  }

}

class test{




   method test_All() 
	{
     /* Init EnrollmentStation */
      var enrollmentStn := new EnrollmentStn.Init();

     /*Low Clearance*/
     var tokenLow := enrollmentStn.Enroll(1,1);
	 assert tokenLow != null;
     assert tokenLow.fingerprint == 1;
     assert tokenLow.clearanceLvl == 1;
     assert tokenLow.valid;
     /*Medium Clearance*/
	 
     var tokenMedium := enrollmentStn.Enroll(2,2);
	 assert tokenMedium != null;
     assert tokenMedium.fingerprint == 2;
     assert tokenMedium.clearanceLvl == 2;
     assert tokenMedium.valid;
	 
     /*High Clearance*/
     var tokenHigh := enrollmentStn.Enroll(3,3);
     assert tokenHigh != null;
     assert tokenHigh.fingerprint == 3;
     assert tokenHigh.clearanceLvl == 3;
     assert tokenHigh.valid;

	/* Token Fail */
	var tokenFailHigh := enrollmentStn.Enroll(5,8);
	var tokenFailLow := enrollmentStn.Enroll(5,-1);
	
	assert tokenFailHigh == null;
	assert tokenFailLow == null;
	
	/* Add Token with existing fingerprint*/
	var tokenExisting := enrollmentStn.Enroll(1,1);	
	assert tokenExisting == null;
	
	/* See if tokens been added to EnrollmentStn*/
	assert enrollmentStn.length == 3;
	assert enrollmentStn.users == {1,2,3};
	
	/* Door-tests */
	
	var IdStnLow := new IdStn.Init(1);
	var IdStnMedium := new IdStn.Init(2);
	var IdStnHigh := new IdStn.Init(3);
	
	/********** Test to open Doors *********/
	
	/*Low securitylvl door */
	
	var accessGranted;
	accessGranted := false;
	assert (IdStnLow.open == false);
	accessGranted := IdStnLow.Open(tokenLow,1);
	assert accessGranted == true;
	assert (IdStnLow.open == true);
	IdStnLow.Close();
	assert (IdStnLow.open == false);
	
	/*Medium securitylvl door */
	
	accessGranted := false;
	assert (IdStnLow.open == false);
	accessGranted := IdStnMedium.Open(tokenMedium,2);
	assert accessGranted == true;
	assert (IdStnMedium.open == true);
	IdStnMedium.Close();
	assert (IdStnMedium.open == false);
	
	/*High securitylvl door */
	
	accessGranted := false;
	assert (IdStnHigh.open == false);
	accessGranted := IdStnHigh.Open(tokenHigh,3);
	assert accessGranted == true;
	assert (IdStnHigh.open == true);
	IdStnMedium.Close();
	assert (IdStnHigh.open == false);
	
	/* Test to open door without access */
	/*Try to open High securitylvl door with too low Access */
	
	accessGranted := false;
	assert (IdStnHigh.open == false);
	accessGranted := IdStnHigh.Open(tokenLow,1);
	assert accessGranted == false;
	assert (IdStnHigh.open == false);
	assert (IdStnHigh.alarm == true);
	assert tokenLow.valid == false;
	IdStnHigh.alarm := false;
	
	/* Test to open door with higher access */
	/*Try to open Low securitylvl door with higher Access than needed */
	
	accessGranted := false;
	assert (IdStnMedium.open == false);
	accessGranted := IdStnMedium.Open(tokenHigh,3);
	assert accessGranted == true;
	assert (IdStnMedium.open == true);
	assert (IdStnMedium.alarm == false);

   }


}
