#
#   hleaps based on Doug Bates's approach and some of his code
#
#   Author: Mark Banghart
#
#   examples of calls
#       out  <- hleaps(y~x1+x2+x3+x1:x2+x2:x3, criteria="R2",
#                     traceModels=TRUE, altOut=TRUE)
#
#       out2  <- hleaps(y~x1+x2+x3+x4+x5+x6+(x1+x2+x3+x4+x5+x6)^2, data=data2,
#                    nBest=5, minSize=2, maxSize=6, timeOut=300)
#
#   Issues to be completed    
#       - Test when a column (but not a term) is NA 
#       - support models with no intercept or block dropping the intercept
#       - profile code to optimize the search loop
#       - limit search to only model sizes that are in the min to max range
#       - Apply a bounded algorithm based on SSMod values
#       - consider other indicators besides order (a 1:n ordering) like percentile
#
#
######################################################################

##  hpmodsetup 
##
##  Does all of what hpmods does except create the matrix of models
##s
##  Modified from Doug Bates hpmods function
##  documentation for which is below
##
##' Determine hierarchy-preserving models
##'
##' Determine the hierarchy-preserving models from a formula
##' @title Hierarchy-preserving models
##' @param formula as in \code{"\link{lm}"}
##' @param data as in \code{"\link{lm}"}
##' @param subset as in \code{"\link{lm}"}
##' @param weights as in \code{"\link{lm}"}
##' @param na.action as in \code{"\link{lm}"}
##' @param offset as in \code{"\link{lm}"}
##' @param \dots optional, additional arguments.  At present, none are used.
##' @return an object of class \code{"hpmods"}
##' @author Douglas Bates
##' @keywords models
##' @examples
##' set.seed(12321)
##' fr  <- data.frame(y = rnorm(900), x1 = rnorm(900), x2 = rnorm(900),
##'                  x3 = gl(3,10,900), x4 = gl(10,3,900))
##' (hpm  <- hpmods(y ~ (x1 + x2 + x3 + x4)^4, fr))
##' @export
##' 

hpmodsetup  <- function(formula, data, subset, weights, na.action, offset, ...) {
  cl    <- match.call()
  mf    <- match.call(expand.dots = TRUE)
  ne    <- c(is.null(formula), missing(data), is.null(subset), is.null(weights), is.null(na.action), is.null(offset))
  theseN     <- c("formula", "data", "subset", "weights", "na.action", "offset")[!ne]
  theseN    <- c("", theseN)
  m     <- match(c("formula", "data", "subset", "weights", "na.action", 
                   "offset"), theseN, 0L)
  
  for(i in 1:length(m)){
    if(i>1){
      if(m[i]!=0){
        m[i] = i+1
      }
    }
  }

  mf    <- mf[c(1L, m)]
  mf$drop.unused.levels  <- TRUE
  mf[[1L]]  <- as.name("model.frame")
  mf    <- eval(mf, parent.frame())
  atts  <- attributes(terms(mf))
  inci  <- crossprod(atts$factor) == atts$order # incidence matrix for terms
  mods  <<- array(FALSE, c(nrow(inci), 1))
  rownames(mods)  <<- rownames(inci)
  mods  <<- t(mods)
  rownames(mods)  <<- mods %*% 2^((seq_len(ncol(inci)))-1)
  res   <<- list(call=cl, incidence=inci, models=mods,
                 frame=mf, X=model.matrix(terms(mf), mf))
  class(res)  <<- "hpmods"
  res
}

hleaps  <- function (formula, 
                     data, 
                     subset=NULL, 
                     weights = NULL, 
                     na.action= NULL, 
                     offset = NULL, 
                     criteria="adjR2",   # critria to be reported
                     nBest=3,            # number of best models per size
                     minSize=NULL,       # smallest size of model reported
                     maxSize=NULL,       # largest size of model reported
                     timeOut=NULL,       # number of seconds to search 
                     #  for models
                     traceModels=FALSE,  # display all models checked as best
                     altOut=FALSE,       # alternate display for output
                     greedy=FALSE,       # use greedy search (slower but
                     #  directed)
                     largeMem=FALSE,     # True if computer has large amount
                     # of memory
                     memAvailable = NULL,   # Amount of memory available for use (GB)
                     ...) {
  
  
  
  ##################################################################################
  #
  #   hleaps code starts here
  #
  ##################################################################################
  #   initial parmeter handling
  #
  cl   <- match.call()
  mf   <- match.call(expand.dots = FALSE)
  m   <- match(c("formula", "data", "subset", "weights", "na.action", 
                 "offset"), names(mf), 0L)
  mf   <- mf[c(1L, m)]
  mf$drop.unused.levels  <- TRUE
  
  #   use lm to determine the number of terms
  #
  
  formula  <- as.formula(formula)  # coerce formula
  if (missing(data)) {
    lmOut  <- lm(formula)
  } else {
    lmOut  <- lm(formula, data=data)
  }
  
  identicals  <<- which(is.na(lmOut$coefficients))
  identicalT  <<- strsplit(names(identicals), ":")
  identicalT  <<- unique(unlist(identicalT))
  numIDSingle  <<- length(identicalT)
  identicalT  <<- unique(c(identicalT, names(identicals[(length(identicalT)):length(identical)])))
  terms  <- attr(lmOut$terms,"term.labels")
  matchTerms  <<- vector()
  for(i in 1:length(identicalT)){
    matchTerms  <<- c(matchTerms,which(terms == identicalT[i]))
  }
  
  termList  <- terms
  numTerms  <<- length(terms)
  
  #   Check that the number of terms is less than or equal to the maximum
  #   number of terms from available memory. If largeMem = TRUE do not calculate
  #
  
  if (is.null(memAvailable)) memAvailable = 1;
  maxTerms  <- floor(log(memAvailable, 2)) + 26
  
  if ( ( numTerms > maxTerms ) & !largeMem) {
    message ("Error - maximum number of terms must be less than ", maxTerms, " - instead of "
             , numTerms)
    terms  <- terms[1:maxTerms]
    numTerms  <<- maxTerms 
    newFormula  <- as.formula(paste(as.character(formula[2]),"~", 
                                    paste(terms, collapse= "+"),
                                    sep=""))
  } else {
    newFormula  <- formula
  }
  
  #   Check parameters and set defaults as needed
  #
  
  if (is.null(minSize)) minSize  <- 1 
  if (is.null(maxSize)) maxSize  <- numTerms
  if (is.null(timeOut)) timeOut  <- Inf
  
  if (!(is.logical(greedy))) {
    message ("Error - greedy must be logical - instead of "
             , greedy)   
    greedy=FALSE
  }
  
  if(!greedy & traceModels) {
    message ("Error - traceModels can only be used with greedy search")
    traceModels = FALSE
  }
  
  if(!is.logical(traceModels)) {
    message ("Error - traceModels must be logical instead of - ",
             traceModels)
    traceModels = FALSE
  }
  
  if(numTerms == 1) {
    message ("Error - number of terms must be greater than 1")
    return();
  }
  
  if(timeOut < 0){
    message ("Error - timeOut must be greater than 0 - instead of ",
             timeOut, " - defaulting timeOut to Inf")
    timeOut=Inf;
  }
  
  if(!is.numeric(timeOut)) {
    message ("Error - timeOut must be numeric - instead of ",
             timeOut, " - defaulting timeOut to Inf")
    timeOut=Inf;
  }
  
  if (!is.logical(largeMem)) {
    message ("Error - largeMem must be logical - instead of ",
             largeMem)
    largeMem = FALSE
  }
  
  if(!is.numeric(memAvailable)) {
    message ("Error - memAvailable must numeric - instead of "
             , memAvailable)
    memAvailable  <- 1
  }
  
  if(memAvailable < 1) {
    message ("Error - must have at least 1 GB available - instead of ",
             , memAvailable)
    
    memAvailable  <- 1
  }
  
  if (minSize >= numTerms) { 
    message ("Error - minSize must be less than number of terms - instead of "
             , minSize)
    minSize  <- 1
  }
  
  if (minSize > numTerms) {
    message ("Error - minSize cannot be greater than the number of possible terms - instead of "
             , minSize, " - defaulting minSize to 1")
    minSize  <- 1
  }
  
  if (minSize < 1) { 
    message ("Error - minSize must be at least 1 - instead of "
             , minSize)
    minSize  <- 1
  }
  
  if (!is.numeric(minSize)) {
    message ("Error - minSize must be at least 1 - instead of "
             , minSize, " - defaulting minSize to 1")
    minSize  <- 1
  }
  
  if(maxSize == 0){
    message("Error - maxSize must be at least 1 - insead of "
            , maxSize)
    max.size  <- numTerms
  }
  if (maxSize  < minSize) { 
    message ("Error - maxSize must be at least as large as minSize - instead of "
             , maxSize)
    maxSize  <- numTerms
  }
  
  if (!is.numeric(maxSize)) {
    message ("Error - maxSize must be at least 1 - instead of "
             , maxSize, " - defaulting maxSize to number of terms")
    maxSize  <- numTerms
  }
  
  if (!(criteria %in% c("adjR2","R2","RSS"))) {
    message ("Error - criteria must me adjR2, R2, or RSS - instead of "
             , criteria, " - criteria defaulting to adjR2")   
    criteria  <- "adjR2"
  }
  if (nBest<1) {
    message ("Error - nBest must be greater than 0 - instead of "
             , nBest)   
    nBest  <- 3
  }    
  
  if (!is.numeric(nBest)) {
    message ("Error - nBest must be numeric - instead of "
             , nBest, " - defaulting to 3")   
    nBest  <- 3
  }
  
  if (!(is.logical(traceModels))) {
    message ("Error - traceModels must be logical - instead of "
             , traceModels)   
    traceModels=FALSE
  }
  
  if(!(is.logical(greedy))) {
    message ("Error - greedy must be logical - instead of "
             , greedy, " - defaulting to FALSE")   
    traceModels=FALSE
  }
  
  if (!(is.logical(altOut))) {
    message ("Error - altOut must be logical - instead of "
             , altOut)   
    altOut=FALSE
  }
  
  #  Create list of models and grouped subsets of models using 
  #  Doug Bates's code and get the needed data
  #
  
  newFormula  <- as.formula(newFormula)  # coerce formula
  
  if (missing(data)) {
    hp  <- hpmodsetup(newFormula, na.action = na.action, offset = offset, subset = subset, weights = weights, ...)
  } else {
    hp  <- hpmodsetup(newFormula, data=data, na.action = na.action, offset = offset, subset = subset, weights = weights,...)
  }
  
  mods <- hp$models
  X  <<- hp$X
  dfTotal  <<- nrow(X)
  incidence  <- hp$incidence
  termLabels  <- attr(attr(hp$frame,"terms"),"term.labels")
  terms  <- seq(1,length(termLabels))
  termOrder  <- attr(attr(hp$frame,"terms"),"order")
  names(termOrder)  <- terms
  respVec  <<- model.response(hp$frame)
  
  #   Decomposition of full model
  #
  
  QR  <- qr(X)
  effList  <- qr.qty(QR,respVec)
  SSIntercept  <<- effList[1]^2
  SSTotal  <<- sum(effList^2)
  colAssign  <<- attr(X,"assign")
  
  #   table to record the Sum of Squares for each model
  #
  maxMods  <- 2^(numTerms)
  SSMod  <<- rep(-1,maxMods)
  
  #   Matrices to record the best Sum of Squares models
  #
  SSModM  <<- matrix(rep(-1,nBest*numTerms), nrow=nBest, ncol=numTerms)
  termsModM  <<- matrix(rep(0,nBest*numTerms), nrow=nBest, ncol=numTerms)
  
  #   search models by subsets for best models
  #
  num.models  <<- 0
  startTime  <<- proc.time()
  outOfTime  <<- FALSE
  
  #   incident table used to find free terms
  #
  if (greedy) {  
    maxOrder  <- max(termOrder)    
    notFree  <- incidence
    rownames(notFree)  <- terms
    colnames(notFree)  <- terms
    for (i in terms) {
      iOrder  <- termOrder[i]
      notFree[(termOrder %in% iOrder:maxOrder),i]  <-0
    }
    
    forcedTerms  <- c("")[-1]
    neededTerms  <- terms
    numSets  <<- 0
    calcSSModGred(neededTerms)   # calc SS for all model
    
    findBest(neededTerms, forcedTerms, traceModels=traceModels, terms=terms, notFree=notFree, timeOut=timeOut)
    
  } else {
    
    #  Create list of models and grouped subsets of models using 
    #   Doug Bates's code     And get the needed data
    #
    
    newFormula  <- as.formula(formula)  # coerce formula
    
    if (missing(data)) {
      hp    <- hpmods(newFormula, ...)
    } else {
      hp   <- hpmods(newFormula, data=data, ...)
    }
    
    mods    <- hp$models
    sets    <- msubs(hp, fr)
    s   <- length(sets)
    numSets   <<- 0
    findBest2(s = s, sets = sets, timeOut = timeOut) 
  }
  
  format.output(minSize, maxSize, nBest, altOut, criteria)
}


#   Calculates Sum of Squares of the Models in a setId subset
#
calcSSMod   <- function (setId, sets) {
  
  set   <- sets[[setId]]
  nSet   <- nrow(set)
  
  #  Create the list of columns needed for largest model of subset
  #
  mod   <- set[nSet,]
  iCols    <- colAssign %in% c(0, which(mod))  # 0 is for intercept 
  
  # select the columns from the R matrix and calculate column effects 
  #
  ared    <- colAssign[iCols]
  thisX   <- X[,iCols]
  QR   <- qr(thisX)
  SS.X   <- qr.qty(QR,respVec)[1:length(iCols)]
  numSets   <<- numSets + 1
  
  
  #  Calculate the SSModel for each model in the subset
  #
  SSCol  <- SS.X^2  
  jSSMod  <- SSCol[1]  # include SS for intercept
  prior.mod  <- rep(FALSE,numTerms)
  
  for (j in rownames(set)) {    
    jNewTerms  <- which(xor(prior.mod,(iTerms  <- set[j,])))
    if (length(jNewTerms) > 0)
    {
      jCols  <- SSCol[which(ared %in% jNewTerms)]
      jSSMod  <- jSSMod + sum(jCols)
    }
    j.modIdx  <- as.integer(j)
    SSMod[j.modIdx]  <<- jSSMod   
    prior.mod  <- iTerms
    
    # store only best subsets apporach
    #
    j.size  <- sum(set[j,])
    if (j.size != 0) {                     # this model null model?
      if ( ( jSSMod > ( j.min  <- min(SSModM[,j.size]) ) ) &
             !(j.modIdx %in% termsModM[,j.size]) # this model already recored?
      ) {                                  
        jRow  <- which(SSModM[,j.size]==j.min)[1]
        SSModM[jRow,j.size]  <<- jSSMod
        termsModM[jRow,j.size]  <<- j.modIdx
      }
    }
  }
}


###########################################################################
#
#   FindBest2 search the subset list in order.
#

findBest2  <- function (s, sets, timeOut) {
  
  #   Find the SSModel for each sub-model with a single free term dropped
  #
  for (i in 1:s) {
    calcSSMod(i, sets)
    begin_lm_time  <- proc.time()
    if ( (begin_lm_time - startTime)[3] > timeOut) {  # over timeOut time?
      message ("Warning - processing time exceeded ", timeOut, 
               "sec partial results have been returned")
      return()
    }
  } 
}

###########################################################################
#
#   format the compressed which matrix of subsets
#

format.subsets  <- function (sdf) {
  numRow  <- nrow(sdf)
  numCol  <- ncol(sdf)
  numDCol  <- numCol%/%5
  if (numCol%%5 > 0) numDCol  <- numDCol + 1
  
  sd  <- data.frame(c(1:numRow))[,-1]  # create an empty data frame
  row  <- 1
  while (row  <= numRow) {
    col  <- 1
    dCol  <- 1
    while (col  <= numCol) {
      if (col+4  < numCol) {
        endCol  <- col+4
      } else {
        endCol  <- numCol
      }
      sd[row,dCol]  <- paste(paste(ifelse(sdf[row,col:endCol]==TRUE,"T",".")), collapse= "")
      col  <- col+5
      dCol  <- dCol+1
    }
    row  <- row + 1
  }
  
  # Create column names
  #
  col  <- 1
  dCol  <- 1
  sdNames  <- c(1)
  while (col  <= numCol) {
    if (col+4  < numCol) {
      endCol  <- col+4
    } else {
      endCol  <- numCol
    }
    this.name  <- c(seq(col+1,endCol))
    this.index  <- this.name[1]%/%10
    this.name  <- this.name%%10
    sdNames[dCol]  <- paste(col,endCol,sep="-")
    col  <- col+5
    dCol  <- dCol+1
  }
  
  names(sd)  <- sdNames

  sd
}


###########################################################################
#
#
#   format the output
#
format.output  <- function(minSize, maxSize, nBest, altOut, criteria) {
  
  # Get best saved models information
  #
  notEmpty  <- as.vector( SSModM >= 0 )      # check if null model
  
  size  <- rep(1:numTerms, each = nBest)[notEmpty]
  SSMod  <<- as.vector(SSModM)[notEmpty]
  #print(cbind(SSMod,SSMod))
  SSRes  <- SSTotal - SSMod
  modId  <- as.vector(termsModM)[notEmpty]
 
  #   Code to convert index to terms (binary) 
  #
  decId  <- modId
  modTerms  <- matrix(ncol=numTerms, nrow=length(decId))
  
  for (i in numTerms:1) {    
    modTerms[,i]  <- decId >= 2^(i-1)
    decId  <- decId - ifelse(modTerms[,i],2^(i-1),0)
  }
  
  dfMod  <- rep(0,length(SSMod))
  
  for (i in 1:length(SSMod)) {
    # 0 is for intercept 
    iCols   <- colAssign %in% c(0, modTerms[i,])
    dfMod[i]  <- sum(as.integer(iCols))
  }
  uSizes = unique(size)

  Moddf  <- dfMod
  otherCol  <- c("size","SSResid","SSModel")
  termsMatrix  <- modTerms

  modOrder  <- order(as.numeric(SSRes))  
  o  <- sort(SSRes)
  modOrder  <- match(SSRes, o)
  print(cbind(modOrder, SSRes))
  RSq  <- (SSMod-SSIntercept) / (SSRes+SSMod)

  # correct if no intercept
  adjRSq  <- 1 - (1 - RSq)*((dfTotal - 1)/(dfTotal-Moddf))
  for(i in 1:length(uSizes)){
    thisSize = which(size == uSizes[i])
    thisSSMod = SSMod[thisSize]
    thisDecSS = order(thisSSMod,decreasing=TRUE)
   
    orderModOrder = modOrder[thisSize]
    modOrder[thisSize] = orderModOrder[thisDecSS]
    
    orderRSq = RSq[thisSize]
    RSq[thisSize] = orderRSq[thisDecSS]

    orderAdjRSq = adjRSq[thisSize]
    adjRSq[thisSize] = orderAdjRSq[thisDecSS]
    
    orderSSRes = SSRes[thisSize]
    SSRes[thisSize] = orderSSRes[thisDecSS]
    
    orderThis = termsMatrix[thisSize,]
    if(length(thisDecSS) > 1){
    termsMatrix[thisSize,] = orderThis[thisDecSS,]
    }
  }

  if (!altOut) {  # if normal output format
    #   Check the critera used
    #
   
    if (criteria=="R2") {
      BSS  <- list(which=termsMatrix, label=colnames(mods), 
                   size=size, Rsquared=RSq)   
    } else if(criteria=="adjR2"){
      BSS  <- list(which=termsMatrix, label=colnames(mods), 
                   size=size, adjRsqrd=adjRSq)  
    } else { 
      BSS  <- list(which=termsMatrix, label=colnames(mods), 
                   size=size, rss=SSRes)   
    } 
    
  } else {   # otherwise alternate formated output
    
    #   compress the which matrix
    #
    comp.mod  <- format.subsets(termsMatrix)
    
    # formate execution info
    #
    totalTime  <- proc.time()[3] - startTime[3]
    time.usage  <- paste("Total number of model subsets examined was ",
                         numSets,
                         " Total run time was ", 
                         format(totalTime,trim = FALSE,digits=7), 
                         " seconds.")
    if (criteria=="R2") {
      modelInfo  <- cbind(size, order=modOrder, RSq, 
                          comp.mod)   
    } else if(criteria=="adjR2"){
      
      modelInfo  <- cbind(size, order=modOrder, adjRSq, 
                          comp.mod)  
    } else { 
      modelInfo  <- cbind(size, order=modOrder, SSRes, 
                          comp.mod)     
    } 
    BSS  <- list(modelInfo=modelInfo, label=colnames(mods),
                 executionInfo=time.usage)
  }
}


###########################################################################
#
#
#   format the output
#
format.output2  <- function(minSize, maxSize, nBest, altOut, criteria) {
  
  #   Order the models based on size of model and SSResid
  #       Then select nBest models of each size
  #
  SSResid  <- SSTotal - SSMod
  modOrder  <- order(sizeMod, SSResid) 

  results  <- data.frame(size=sizeMod[modOrder], 
                         SSResid=SSResid[modOrder], 
                         SSModel=SSMod[modOrder],
                         modId=modOrder 
  )
  
  #   Remove models that are not in the best nBest for each size
  #
  all  <- results
  for (i in 0:numTerms) {
    sizeLst  <- which(results[,"size"] %in% i)
    if (i  < minSize) {
      results  <- results[-sizeLst,]
    }
    else if (i > maxSize) {
      results  <- results[-sizeLst,]
    }
    else if (length(sizeLst) > nBest) 
    {
      toDel  <- sizeLst[-c(1:nBest)]
      results  <- results[-toDel,]
    }
  }
  
  size  <- results[,"size"]
  SSRes  <- results[,"SSResid"]
  SSMod  <<- results[,"SSModel"]
  modId  <- results[,"modId"]
  
  #   Code to convert index to terms (binary) 
  #
  
  decId  <- modId
  modTerms  <- matrix(ncol=numTerms, nrow=nrow(results))
  for (i in numTerms:1) {    
    modTerms[,i]  <- decId >= 2^(i-1)
    decId  <- decId - ifelse(modTerms[,i],2^(i-1),0)
  }
  
  dfMod  <- rep(0,nrow(results))
  for (i in 1:nrow(results)) {
    # 0 is for intercept 
    iCols   <- colAssign %in% c(0, modTerms[i,])
    dfMod[i]  <- sum(as.integer(iCols))
  }
  
  Moddf  <- dfMod
  otherCol  <- c("size","SSResid","SSModel")
  termsMatrix  <- modTerms
  modOrder  <- order(SSRes) 

  RSq  <- (SSMod-SSIntercept) / (SSRes+SSMod)
  
  # correct if no intercept
  adjRSq  <- 1 - (1 - RSq)*((dfTotal - 1)/(dfTotal-Moddf))
  
  if (!altOut) {  # if normal output format
    #   Check the critera used
    #
    if (criteria=="R2") {
      BSS  <- list(which=termsMatrix, label=colnames(mods), 
                   size=results[,"size"], Rsquared=RSq)   
    } else if(criteria=="adjR2"){
      BSS  <- list(which=termsMatrix, label=colnames(mods), 
                   size=results[,"size"], adjRsqrd=adjRSq)  
    } else { 
      BSS  <- list(which=termsMatrix, label=colnames(mods), 
                   size=results[,"size"], rss=SSRes)   
    } 
    
  } else {   # otherwise alternate formated output
    
    #   compress the which matrix
    #
    comp.mod  <- format.subsets(termsMatrix)
    
    # formate execution info
    #
    totalTime  <- proc.time()[3] - startTime[3]
    time.usage  <- paste("Total number of model subsets examined was ",
                         numSets,
                         " Total run time was ", 
                         format(totalTime,trim = FALSE,digits=7), 
                         " seconds.")
    if (criteria=="R2") {
      modelInfo  <- cbind(size, order=modOrder, RSq, 
                          comp.mod)   
    } else if(criteria=="adjR2"){
      modelInfo  <- cbind(size, order=modOrder, adjRSq, 
                          comp.mod)  
    } else { 
      modelInfo  <- cbind(size, order=modOrder, SSRes, 
                          comp.mod)     
    } 
    BSS  <- list(modelInfo=modelInfo, label=colnames(mods),
                 executionInfo=time.usage)
  }
}


#   Used for the greedy search algorithm
#   Calculates sum of squares for all the possible nested models  
#       within the current set of terms.  It may recalculate the
#       sum of squares for nested models.
#   The terms must be provided in the sorted with the lowest ordered
#       terms first to the highet ordered terms
#
calcSSModGred  <- function (terms) {
  
  #  Create the list of columns needed for largest model
  #
  iCols   <- colAssign %in% c(0, terms)  # 0 is for intercept 
  
  # select the columns from the X matrix and calculate column effects 
  #
  ared   <- colAssign[iCols]   # column assignments for this model
  thisX  <- X[,iCols]
  QR  <- qr(thisX)
  #if(QR$rank != ncol(thisX)) error()
  SS.X  <- qr.qty(QR,respVec)[1:length(iCols)]
  
  #  Calculate the SSModel for each model in the subset
  #
  SSCol  <- SS.X^2  
  jSSMod  <- SSCol[1]  # include SS for intercept
  termIds  <- terms
  nSet  <- length(terms)
  numSets   <<- numSets + 1

  for (j in 1:nSet) {  # for each term of terms
    jTerm  <- termIds[j]
    # which columns to sum for this term
    jCols  <- SSCol[which(ared %in% jTerm)]  
    # cumulative sum for terms so far 
    jSSMod  <- jSSMod + sum(jCols)
    #
    iModIdx  <- sum(2^(terms[1:j]-1))
    SSMod[iModIdx]  <<- jSSMod        
    
    # store only best subsets apporach
    #
    if ( ( jSSMod > ( j.min  <- min(SSModM[,j]) ) ) &
           !(iModIdx %in% termsModM[,j]) ) { # this model
      jRow  <- which(SSModM[,j]==j.min)[1]
      SSModM[jRow,j]  <<- jSSMod
      termsModM[jRow,j]  <<- sum(2^(terms[1:j]-1))
    }
  }
}


##########################################################################
#
#   FindBest recursively calls it self with the most significant term dropped and forced
#   The most significant term is found by calculating the subset models of all free terms
#

findBest  <- function (thisTerms,   # ordered list of terms in model 
                       thisForced,  # list of terms forced into model
                       forced=FALSE, # Indicator for forced call
                       forcedFreeSS, # list of SS for free terms if force
                       traceModels,
                       terms,
                       notFree,
                       timeOut) 
{
  if ( length(thisTerms)  <= 0) return()  # bad call if no predictors
  # in the model
  
  if (!forced) {
    if (traceModels) {   # traceModels displays each model that is passed to findBest
      num.models  <<- num.models + 1
      message("Check: ", format(num.models,trim = FALSE,width=4), 
              #                    " RSS: ", format(this.RSS,trim = FALSE,width=8,digits=7), 
              "  ", format(length(thisTerms),trim = FALSE,width=2), 
              "  terms: ", paste(c(thisTerms),collapse=", "), 
              " - - forced terms: ", paste(c(thisForced),collapse=", "))
    }
    
    #   Find the list of terms that are free to be dropped
    #  the following line is not to be checked
    #
    
    this.noForce  <- setdiff(thisTerms,thisForced)
    if (length(thisTerms) > 1) {
      thisNotFree  <- notFree[,thisTerms]
      freeRows  <- (rowSums(thisNotFree) == 0)
      thisFree  <- terms[freeRows]
      free  <- thisFree[(thisFree %in% this.noForce)]
    } else {
      free  <- thisTerms
    }
    
    if (length(free)==0) return()  # no terms to drop or force
    
    #   Find the SSModel for each sub-model with a single 
    #   free term dropped
    #
    
    freeSS  <-c(0)[-1]
    if (length(thisTerms)>1) {
      for (i in free) {
        
        #   find the model id for the model with the dropped
        #   free term
        #
        iTerms  <- thisTerms[thisTerms != i]
        iModIdx  <- sum(2^(iTerms-1))
        
        #   if no SSMod for this model, calculate the SSMod for the subset which included it
        #
        
        if (SSMod[iModIdx]  < 0) calcSSModGred(iTerms)
        
        #   add to the list of SSMods for the free terms
        #
        
        iMod  <- SSMod[iModIdx]
        names(iMod)  <- i
        freeSS  <- c(freeSS,iMod)
      }
    }  
  } else {       
    #  if forced, used the SSModels calculated at the
    #  above level
    
    freeSS  <- forcedFreeSS
  }
  
  thisTime  <- proc.time()
  if ( (thisTime - startTime)[3] > timeOut) {  # over timeOut time?
    if (outOfTime == FALSE) {
      message ("Warning - processing time exceeded ", timeOut, 
               " partial results have been returned")
    }
    outOfTime  <<- TRUE
    return()
  }
  
  if (length(freeSS)==0) return()  # no terms to drop or force
  
  #   find the best model of the set of dropped free terms
  #   which is the model which is least significant
  #          
  
  signfFree  <- names(which( freeSS == min(freeSS))[1] )[1] 
  
  #   If there are terms after dropping, continue dropping
  #   & forcing terms
  #
  newTerms  <- thisTerms[-which(thisTerms==signfFree)]
  
  if ( length(newTerms) >= 1 ) {   # are there terms to drop
    # or force?
    # drop the term first
    findBest(newTerms, thisForced, traceModels = traceModels, terms=terms, notFree=notFree, timeOut=timeOut)    
    #    force the least significant term into the model
    newForced  <- c(thisForced, signfFree)
    newFreeSS  <- freeSS[-which(names(freeSS)==signfFree)]
    findBest(thisTerms, newForced, forced=TRUE,
             forcedFreeSS=newFreeSS, traceModels = traceModels, terms = terms, notFree=notFree, timeOut=timeOut)     
  }
}
