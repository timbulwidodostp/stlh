*! version 1.0.0 DWH/PR 08Mar2002.    (SJ2-4: st0024)
program define stlh
version 6
st_is 2 analysis
syntax varlist(min=1) [if] [in], [ noDOTs GENerate(string) noGRAph LEVel(string) /*
 */ noMORE SAVing(string) TCent(real 75) TESTwt(numlist >=1 <=4 integer sort) * ]
if "`saving'"!="" {
	tokenize "`saving'", parse(" ,")
	local s `1'
	local replace `2'`3'
	if "`4'"!="" | ("`replace'"!="" & "`replace'"!=",replace") {
		di in red "invalid saving(`saving')"
		exit 198
	}
	local saving `s'
}
* key st chars
local id: char _dta[st_id]
local wt: char _dta[st_wt]      /* type of weight */
if "`wt'"!="" {
	di in red "weights not supported"
	exit 198
}
local time _t
local t0 _t0
local dead _d

if `tcent'>100 | `tcent'<10 {
	di in red "tcent() must be between 10 and 100 (default is 75)"
	exit 198
}
if "`level'"!="" {
	confirm num `level'
}
else local level $S_level
tempname zlevel
scalar `zlevel'=-invnorm((100-`level')/200)

if "`graph'"=="nograph" & "`saving'"!="" {
	di in red "no graphs to save"
	exit 198
}

quietly {
	marksample touse
	markout `touse' `varlist'
	replace `touse'=0 if _st==0
	count if `touse'
	local nobs=r(N)
	if "`graph'"!="nograph" & `tcent'<100 {
		centile `time', centile(`tcent')
		local tp=r(c_1)
		local iftc "& `time'<=`tp'"
	}
	* Remove collinearities
	noi _rmcoll `varlist' if `touse'
	local varlist `r(varlist)'
	local nx: word count `varlist' 
	local p 0
	while  `p'<=`nx' {
		local p=`p'+1
		if `p'>`nx' {
			local nm`p' "_cons"
		}
		else local nm`p': word `p' of `varlist'
		tempvar a`p'
		gen `a`p''=.
		if "`generat'"!="" {
			confirm new var `generat'A`p'
			confirm new var `generat'S`p'
		}
	}
	noi di in gr _n "Graphs and tests for Aalen's Additive Model" _n _dup(43) "-"
	noi di in gr "Model:  " in ye "`varlist'"
	noi di in gr "Obs:    " in ye `nobs' _n
	local Np=`nobs'-`p'
	* Handle possible ties by sorting data in order of time, censoring, covariates.
	* Covariates are ordered lexicographically, so results can never change even
	* if covariates are ordered differently on input.
	listsort "`varlist'", lexicographic
	local vlsort `s(list)'
	* put obs with missing last then drop them
	gsort -`touse' `time' -`dead' `vlsort'
	local todrop=`nobs'<_N
	if `todrop' {
		preserve
		if "`generat'"!="" {
			tempfile orig
			save `orig'
		}
		drop if `touse'==0
	}
	tempvar dN
	gen byte `dN'=0
	local it 1
	while `it'<=`Np' {  /* begin it loop */ 
		if "`dots'"!="nodots" {
			if mod(`it',100)==0 { noi di in gr "." _continue }
		}
		if `dead'[`it']==1 {   /* begin dead==1 loop */   
			replace `dN'=(_n==`it')
			* regress for any obs for which time>=current failure time
			* and entry time (t0) is earlier than current failure time
			capture regress `dN' `varlist' if _n>=`it' & `t0'<`time'[`it']
			if e(df_m)==`nx' {  /* full rank; regression can continue */        
				local k 1
				while `k'<=`p' {
					replace `a`k''=_b[`nm`k''] in `it'
					local k=`k'+1
				}
			} /* end of rss>0 */
		} /* end of the dead==1 loop */ 
		local it=`it'+1 
	} /* end it loop */
	noi di 
	local k 1
	while `k'<=`p' {
		tempvar A`k' VA`k'
		gen `A`k''=sum(`a`k'')
		gen `VA`k''=sum(`a`k''^2)
		*replace `a`k''=. if `dead'==0
		local k=`k'+1
	}
	if "`graph'"!="nograph" {
		* Graph
		if "`more'"!="nomore" {
			set more on
		}
		tempvar lb ub
		gen `lb'=.
		gen `ub'=.
		local k 1
		while `k'<=`p' {
			local t1
			if `k'<`p' {	/* k=p is _cons */
				local t1: var label `nm`k''
				if "`t1'"=="" { 
					local t1 `nm`k''
				} 
			}
			else local t1 [Constant]
			replace `lb'=`A`k''-`zlevel'*sqrt(`VA`k'') if `dead'==1
			replace `ub'=`A`k''+`zlevel'*sqrt(`VA`k'') if `dead'==1
			if "`saving'"!="" {
				local sav saving(`saving'`nm`k''`replace')
			}
			graph `lb' `A`k'' `ub' `time' if `a`k''!=. `iftc', sort /*
			 */ pen(323) s(iii) c(JJJ) `sav' t1title(`t1') yline(0) `options'
			if "`more'"!="nomore" & `k'<`p' {
				more
			}
			local k=`k'+ 1
		}
	}
	* hypothesis test(s), if specified
	local ntest: word count `testwt'
	if `ntest'>0 {
		local maxtst: word `ntest' of `testwt'
		if `maxtst'>=3 {
			tempvar SKM
			sts gen `SKM'=s
		}
		tempvar Asm AsmV zwt
		gen `Asm'=.
		gen `AsmV'=.
		gen `zwt'=.
		gsort `time' -`dead' `vlsort'
		tokenize `testwt'
		while "`1'"!="" {
			local w `1'
			if `w'==1  	{
				local wtt`w' "1.0"
				replace `zwt'=1
			}
			else if `w'==2 {
				local wtt`w' "the Size of the Risk Set"
				replace `zwt'=_N-_n+1
			}
			else if `w'==3 {
				local wtt`w' "Kaplan-Meier Estimator at Time t-"
				replace `zwt'=cond(_n==1, 1, `SKM'[_n-1])
			}
			else {
				local wtt`w' "(Kaplan-Meier Estimator at Time t-)/(Std. Dev of the Time-varying Coefficient)"
			}
			local k 1
			while `k'<=`p' {
				if  `w'==4  {
					replace `zwt'=cond(_n==1, 1, `SKM'[_n-1])/abs(`a`k'')
				}
				replace `Asm'=sum(`a`k''*`zwt') 
				replace `AsmV'=sum((`a`k''*`zwt')^2)
				local z`k'=`Asm'[_N]/sqrt(`AsmV'[_N])
				local k=`k'+ 1
			}
			noisily {
				di in gr _n "Test `w': Uses Weights Equal to" _n "`wtt`w''" _n
				di in gr "Variable" _col(17) "z" _col(27) "P"
				di in gr "-----------------------------"
				local k 1
				while `k'<=`p' {
					di in gr "`nm`k''" in ye _col(13) %7.3f `z`k'' /*
					 */ _col(25) %5.3f 2*(1-normprob(abs(`z`k'')))
					local k=`k'+1
				}
			}
			mac shift /* to process next requested test number */
		}
	} /* end of loop for hypothesis tests */
	if "`generat'"!="" {
		local keep
		local k 1
		while `k'<=`p' {
			gen `generat'S`k'=sqrt(`VA`k'')
			rename `A`k'' `generat'B`k'
			lab var `generat'B`k' "Aalen cum coeff for `nm`k''"
			lab var `generat'S`k' "SE(Aalen cum coeff for `nm`k'')"
			local keep `keep' `generat'B`k' `generat'S`k'
			local k=`k'+1
		}
		if `todrop' {
			tempfile addits
			keep `keep'
			save `addits'
			use `orig'
			merge using `addits'
			drop _merge
			restore, not
		}
	}
} /* end quietly */
end

*! version 1.0.0 PR 16Feb2001.
program define listsort, sclass
version 6
gettoken p 0 : 0, parse(" ,")
if `"`p'"'=="" {
	exit
}
sret clear
syntax , [ Reverse Lexicographic ]
local lex="`lexicog'"!=""
if "`reverse'"!="" { local comp < }
else local comp >
local np: word count `p'
local i 1
while `i'<=`np' {
	local p`i': word `i' of `p'
	if !`lex' { confirm number `p`i'' }
	local i=`i'+1
}
* Apply shell sort (Kernighan & Ritchie p 58)
local gap=int(`np'/2)
while `gap'>0 {
	local i `gap'
	while `i'<`np' {
		local j=`i'-`gap'
		while `j'>=0 {
			local j1=`j'+1
			local j2=`j'+`gap'+1
			if `lex' { local swap=(`"`p`j1''"' `comp' `"`p`j2''"') }
			else local swap=(`p`j1'' `comp' `p`j2'')
			if `swap' {
				local temp `p`j1''
				local p`j1' `p`j2''
				local p`j2' `temp'
			}
			local j=`j'-`gap'
		}
		local i=`i'+1
	}
	local gap=int(`gap'/2)
}
local p
local i 1
while `i'<=`np' {
	sret local i`i' `p`i''
	local p `p' `p`i''
	local i=`i'+1
}
sret local list `p'
end
