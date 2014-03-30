import os, sys, re, time, gzip
import urllib, urllib2, httplib
from BeautifulSoup import BeautifulSoup
import MySQLdb
from threading import Thread
#import simplejson as json
import wx
from urlparse import urlparse, urlsplit
from StringIO import StringIO
import mimetypes, mimetools


"""
Some utility function definitions
"""
def urlEncodeString(s):
    tmphash = {'str' : s }
    encodedStr = urllib.urlencode(tmphash)
    encodedPattern = re.compile(r"^str=(.*)$")
    encodedSearch = encodedPattern.search(encodedStr)
    encodedStr = encodedSearch.groups()[0]
    encodedStr = encodedStr.replace('.', '%2E')
    encodedStr = encodedStr.replace('-', '%2D')
    encodedStr = encodedStr.replace(',', '%2C')
    return (encodedStr)

def encode_multipart_formdata(fields):
    BOUNDARY = mimetools.choose_boundary()
    #BOUNDARY = '---------------------------146043902159'
    CRLF = '\r\n'
    L = []
    for (key, value) in fields.iteritems():
        L.append('--' + BOUNDARY)
        L.append('Content-Disposition: form-data; name="%s"' % key)
        L.append('')
        L.append(value)
    L.append('--' + BOUNDARY + '--')
    L.append('')
    body = CRLF.join(L)
    #content_type = 'Content-Type: multipart/form-data; boundary=%s' % BOUNDARY
    content_type = 'multipart/form-data; boundary=%s' % BOUNDARY
    #content_length = 'Content-Length: ' + str(len(body)) + CRLF
    content_length = str(len(body))
    return content_type, content_length, body


def getTimeStampString():
    ts = time.time()
    ts_str = int(ts).__str__()
    return (ts_str)


class NoRedirectHandler(urllib2.HTTPRedirectHandler):
    def http_error_302(self, req, fp, code, msg, headers):
        infourl = urllib.addinfourl(fp, headers, req.get_full_url())
        infourl.status = code
        infourl.code = code
        return infourl

    http_error_300 = http_error_302
    http_error_301 = http_error_302
    http_error_303 = http_error_302
    http_error_307 = http_error_302 



# The  'OdeskBot' class is the main class that emulates the activities of the odesk bot.
# An 'OdeskBot' object by and large goes through the following phases (not an exhaustive list):
# 1. The 'OdeskBot' object comes to odesk website - navigates to the login page of the website.
# 2. The 'OdeskBot' object tries to login into odesk by authenticating herself/himself with the user Id and password.
# 3. The 'OdeskBot' object is capable of performing a reasonably large variety of operations. Some of these
#    are (a) bidding on a project, (b) replying to a message from a client, (c) taking tests, (d) profile
#    completion/editing, (e) clicking on the activation link in the email for confirming user creation process,
#    (f) filling up of a captcha challenge , (g) sending reminders to client after a bid request has already been
#    made, (h) selecting a job to bid on from the list of available jobs, (i) logging out of an account, etc.

class OdeskBot(object):
    """
    Define some  class level variables.
    """
    absUrlPattern = re.compile(r"^https?:\/\/", re.IGNORECASE)
    htmlTagPattern = re.compile(r"<[^>]+>", re.MULTILINE | re.DOTALL)
    newlinePattern = re.compile(r"\n")
    multipleWhitespacePattern = re.compile(r"\s+")
    pathEndingWithSlashPattern = re.compile(r"\/$")
    emptyStringPattern = re.compile(r"^\s*$", re.MULTILINE | re.DOTALL)
    quotePattern = re.compile(r"['\"]", re.MULTILINE|re.DOTALL)

    htmlEntitiesDict = {'&nbsp;' : ' ', '&#160;' : ' ', '&amp;' : '&', '&#38;' : '&', '&lt;' : '<', '&#60;' : '<', '&gt;' : '>', '&#62;' : '>', '&apos;' : '\'', '&#39;' : '\'', '&quot;' : '"', '&#34;' : '"'}
    # Set DEBUG to False on prod env
    DEBUG = True
    
    # Constructor
    def __init__(self, websiteUrl="https://www.odesk.com/"):
        self.opener = urllib2.build_opener() # This is my normal opener....
        self.no_redirect_opener = urllib2.build_opener(urllib2.HTTPHandler(), urllib2.HTTPSHandler(), NoRedirectHandler()) # this one won't handle redirects.
        #self.debug_opener = urllib2.build_opener(urllib2.HTTPHandler(debuglevel=1))
        # Initialize some object properties.
        self.sessionCookies = ""
        self.httpHeaders = { 'User-Agent' : r'Mozilla/5.0 (Windows NT 6.1; WOW64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/27.0.1453.110 Safari/537.36',  'Accept' : 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8', 'Accept-Language' : 'en-US,en;q=0.8', 'Accept-Encoding' : 'gzip,deflate,sdch', 'Connection' : 'keep-alive', 'Host' : 'www.odesk.com', 'Referer' : 'https://www.odesk.com/' }
        self.homeDir = os.getcwd()
        if not re.search(self.__class__.pathEndingWithSlashPattern, websiteUrl):
            websiteUrl += "/"
        self.websiteUrl = websiteUrl
        self.loginUrl = self.websiteUrl + "login"
        self.username = ""
        self.password = ""
        self.requestUrl = None
        if re.search(re.compile(r"^https?:\/\/"), self.loginUrl):
            self.requestUrl = self.loginUrl
        self.pageRequest = None
        self.pageResponse = None
        self.requestMethod = "GET"
        self.postData = {}
        self.multipleChoiceFlag = False # By default it is false and the user is presented with the radio button interface. If it is made true, the user is presented with the checkbox interface.
        self.sessionCookies = None
        self.cookiesDict = {}
        self.currentPageContent = None
        parsedUrl = urlparse(self.requestUrl)
        self.baseUrl = parsedUrl.scheme + "://" + parsedUrl.netloc
        self.visitor_id = ""
        self.leaving_odesk_auto = 1
        self.allTests = {}
        self.reanswer = 0 # Default, it is set to 0 so that questions having an answer in the database are not shown to the user.
        self.selectedTest = None
        self.testObject = Test() # This is a 'Test' object that will be loaded when the 'getTest' method is called from 'GUIWrapper' class.
        # List of links to pages we need to navigate to in order to extract the desired data
        self.testsUrl = ""
        self.testExistsInDB = 0
        self.dbconn = MySQLdb.connect("localhost", "root", "spmprx", "odesktestpapers") # Connection to the odesktestpapers database
        self.cursor = self.dbconn.cursor()
        # Here we just get the webpage pointed to by the website URL
        self.pageRequest = urllib2.Request(self.requestUrl, None, self.httpHeaders)
        if re.search(re.compile(r"^https?:\/\/"), self.loginUrl):
            try:
                self.pageResponse = self.no_redirect_opener.open(self.pageRequest)
                self.sessionCookies = self.__class__._getCookieFromResponse(self.pageResponse)
                self.httpHeaders["Cookie"] = self.sessionCookies
            except:
                print __file__.__str__() + ": Couldn't fetch page due to limited connectivity. Please check your internet connection and try again - %s\n"%(sys.exc_info()[1].__str__())
	    	return(None)
	    self.httpHeaders["Referer"] = self.requestUrl
            self.httpHeaders["Cache-Control"] = 'max-age=0'
            self.httpHeaders["Origin"] = 'https://www.odesk.com'
            self.httpHeaders["Content-Type"] = 'application/x-www-form-urlencoded'
        else:
            self.requestUrl = self.baseUrl + self.loginUrl
            self.pageRequest = urllib2.Request(self.requestUrl, None, self.httpHeaders)
            try:
                self.pageResponse = self.no_redirect_opener.open(self.pageRequest)
                self.sessionCookies = self.__class__._getCookieFromResponse(self.pageResponse)
                self.httpHeaders["Cookie"] = self.sessionCookies
            except:
                print __file__.__str__() + ": Couldn't fetch page due to limited connectivity. Please check your internet connection and try again - %s\n"%(sys.exc_info()[1].__str__())
	    	return(None)

	    

    def login(self, username=None, password=None, loginUrl = r"https://www.odesk.com/login"):
        if not username and self.username is None:
            print "Cannot login into oDesk - no username provided.\n"
            return None
        if not password and self.password is None:
            print "Cannot login into oDesk - no password provided.\n"
            return None
        if username:
            self.username = username
        if password:
            self.password = password
        self.requestMethod = "POST"
        self.loginUrl = loginUrl
        self.requestUrl = self.loginUrl
        self.postData = { 'username' : self.username, 'password' : self.password, 'remember_me' : '0', 'ioBB' : '' }
        if self.requestMethod == 'POST':
            encodedPostData = urllib.urlencode(self.postData)
        self.httpHeaders['Content-Length'] = encodedPostData.__len__()
        self.httpHeaders['Referer'] = loginUrl
        self.pageRequest = urllib2.Request(self.requestUrl, encodedPostData, self.httpHeaders)
        try:
            self.pageResponse = self.no_redirect_opener.open(self.pageRequest)
            self.sessionCookies = self.__class__._getCookieFromResponse(self.pageResponse)
        except:
            print __file__.__str__() + ": The connection is not working right now... Will wait for a little while before trying again. - %s\n"%(sys.exc_info()[1].__str__())
            return None
        responseHeaders = self.pageResponse.info()
        if responseHeaders.has_key('Location'):
            self.httpHeaders['Referer'] = self.requestUrl
            self.requestUrl = responseHeaders['Location']
            if not re.search(re.compile(r"^https?:\/\/"), self.requestUrl):  # The self.requestUrl starts with 'https?:\/\/...'
                self.requestUrl = self.baseUrl + self.requestUrl
            self.httpHeaders['Cookie'] = self.sessionCookies
            self.httpHeaders["Cache-Control"] = 'max-age=0'
            self.httpHeaders['Connection'] = 'keep-alive'
        else:
            self.requestUrl = None
        if not self.requestUrl:
            print "Could not find the redirect URL on POST request.\n"
            return None
        self.pageRequest = urllib2.Request(self.requestUrl, None, self.httpHeaders)
        try:
            self.pageResponse = self.no_redirect_opener.open(self.pageRequest)
            self.sessionCookies = self.__class__._getCookieFromResponse(self.pageResponse)
        except:
            print __file__.__str__() + ": The connection is not working right now... Will wait for a little while before trying again. - %s\n"%(sys.exc_info()[1].__str__())
            return None
        responseHeaders = self.pageResponse.info()
        if responseHeaders.has_key('Location'):
            self.httpHeaders['Referer'] = self.requestUrl
            self.requestUrl = responseHeaders['Location']
            if not re.search(re.compile(r"^https?:\/\/"), self.requestUrl):
                self.requestUrl = self.baseUrl + self.requestUrl
            self.httpHeaders['Cookie'] = self.sessionCookies
            self.httpHeaders["Cache-Control"] = 'max-age=0'
            self.httpHeaders['Connection'] = 'keep-alive'
        else:
            self.requestUrl = None
        if not self.requestUrl:
            print "Could not find the redirect URL on POST request.\n"
            return None
        self.pageRequest = urllib2.Request(self.requestUrl, None, self.httpHeaders)
        try:
            self.pageResponse = self.no_redirect_opener.open(self.pageRequest)
            self.sessionCookies = self.__class__._getCookieFromResponse(self.pageResponse)
            self.cookiesDict = self.populateCookiesDict(self.pageResponse)
        except:
            print __file__.__str__() + ": The connection is not working right now... Will wait for a little while before trying again. - %s\n"%(sys.exc_info()[1].__str__())
            return None
        responseHeaders = self.pageResponse.info()
        if responseHeaders.has_key('Location'):
            self.httpHeaders['Referer'] = self.requestUrl
            self.requestUrl = responseHeaders['Location']
            if not re.search(re.compile(r"^https?:\/\/"), self.requestUrl):
                self.requestUrl = self.baseUrl + self.requestUrl
            self.httpHeaders['Cookie'] = self.sessionCookies
        else:
            self.requestUrl = None
            return None
        self.pageRequest = urllib2.Request(self.requestUrl, None, self.httpHeaders)
        self.httpHeaders['Referer'] = self.requestUrl
        self.httpHeaders["Cache-Control"] = 'max-age=0'
        self.httpHeaders['Connection'] = 'keep-alive'
        try:
            self.pageResponse = self.no_redirect_opener.open(self.pageRequest)
            self.sessionCookies = self.__class__._getCookieFromResponse(self.pageResponse)
            self.populateCookiesDict(self.pageResponse)
            self.httpHeaders['Cookie'] = self.sessionCookies
        except:
            print __file__.__str__() + ": The connection is not working right now... Will wait for a little while before trying again. - %s\n"%(sys.exc_info()[1].__str__())
            return None
        self.currentPageContent = self.__class__._decodeGzippedContent(self.getPageContent())
        if not self.currentPageContent:
            print "Could not access the website content of: '" + self.requestUrl + "'...\n\n-------------------------\n\n"
            return None
        else:
            return (self.currentPageContent)


        

    def setCredentials(self, username, password):
        self.username = username
        self.password = password



    def getTestLink(self):
        soup = BeautifulSoup(self.currentPageContent.__str__())
        allNavAnchors = soup.findAll("a", {'class' : 'oNavLink'})
        testsUrl = ""
        self.testsUrl = testsUrl
        for navAnchor in allNavAnchors:
            anchorText = navAnchor.getText()
            if anchorText == u"Tests":
                anchorUrl = navAnchor['href']
                if not re.search(re.compile(r"^https?:\/\/"), anchorUrl):
                    testsUrl = self.baseUrl + anchorUrl
                else:
                    testsUrl = anchorUrl
                self.testsUrl = testsUrl
                return(testsUrl)
        if self.testsUrl == "":
            print "It seems that the user identified as '%s' has not yet completed creating the profile with the basic details yet. So it is not possible to navigate to the 'tests' link. Please complete the profile and try again.\n"%(self.username)
            return None
        return(testsUrl)


    def getPage(self, url):
        self.requestUrl = url.strip()
        nextUrl = self.requestUrl
        multipleSemicolonsPattern = re.compile(";\s*;")
        while nextUrl:
            self.httpHeaders['Cookie'] = self.httpHeaders['Cookie'].strip()
            self.httpHeaders['Cookie'] = self.sessionCookies + ";"
            self.httpHeaders['Cookie'] += self.createCookieStringFromDict()
            while re.search(multipleSemicolonsPattern, self.httpHeaders['Cookie']):
                self.httpHeaders['Cookie'] = re.sub(multipleSemicolonsPattern, "; ", self.httpHeaders['Cookie'])
            self.pageRequest = urllib2.Request(nextUrl, None, self.httpHeaders)
            try:
                self.pageResponse = self.no_redirect_opener.open(self.pageRequest)
                self.sessionCookies = self.__class__._getCookieFromResponse(self.pageResponse)
                self.httpHeaders['Referer'] = self.requestUrl
                responseHeaders = self.pageResponse.info()
                if responseHeaders.has_key('Location'):
                    self.requestUrl = self.baseUrl + responseHeaders['Location']
                    nextUrl = self.requestUrl
                    continue
                else:
                    nextUrl = None
            except:
                responseHeaders = self.pageResponse.info()
                if responseHeaders.has_key('Location'):
                    self.httpHeaders['Referer'] = self.requestUrl
                    self.requestUrl = responseHeaders['Location']
                    if not re.search(self.__class__.absUrlPattern, responseHeaders['Location']):
                        self.requestUrl = self.baseUrl + responseHeaders['Location']
                    nextUrl = self.requestUrl
                    continue
                else:
                    print __file__.__str__() + ": The connection is not working right now... Will wait for a little while before trying again. - %s\n"%(sys.exc_info()[1].__str__())
                    return None
        self.currentPageContent = self.__class__._decodeGzippedContent(self.getPageContent())
        if not self.currentPageContent:
            print "Could not access the website content of: '" + self.requestUrl + "'...\n\n-------------------------\n\n"
            return None
        else:
            return (self.currentPageContent)
        

    """
    Extracts all tests available on odesk. Handles pagination too.
    """
    def getAllTests(self):
        moreTestsPageContent = self.currentPageContent
        if re.search(re.compile(r"View\s+more\s+tests", re.IGNORECASE | re.MULTILINE | re.DOTALL), self.currentPageContent): # So we are in the page where only tests appropriate for the logged in user are listed.
            soup = BeautifulSoup(self.currentPageContent)
            alloBtnLinks = soup.findAll("a", {'class' : 'oBtn'})
            moreTestsPageLink = ""
            for btnLink in alloBtnLinks:
                linkText = btnLink.getText()
                if linkText == r"View more tests":
                    moreTestsPageLink = btnLink['href']
                    if not re.search(re.compile(r"^https?:\/\/"), moreTestsPageLink):
                        moreTestsPageLink = self.baseUrl + moreTestsPageLink
                    break
            allTests = {}
            # First, parse this page to retrieve all the tests listed on this page
            allTestAnchors = soup.findAll("a", {'class' : 'oTxtMed'})
            for testAnchor in allTestAnchors:
                testTitle = testAnchor.getText()
                testTitle = testTitle.strip()
                testUrl = testAnchor['href']
                if not re.search(re.compile(r"^https?:\/\/"), testUrl):
                    testUrl = self.baseUrl + testUrl
                allTests[testTitle] = testUrl
            # Now, navigate to the "View more tests" page
            self.httpHeaders['Referer'] = self.requestUrl
            self.httpHeaders['Cookie'] += self.createCookieStringFromDict()
            moreTestsPageContent = self.getPage(moreTestsPageLink)
        # Handle pagination
        nextPageLinkPattern = re.compile("\/tests\?skip=\d+", re.MULTILINE | re.DOTALL)
        self.allTests = {}
        while 1:
            testSoup = BeautifulSoup(moreTestsPageContent)
            allTestTDs = testSoup.findAll("td", {'class' : 'test_name'})
            if allTestTDs.__len__() == 0:
                break
            for testTD in allTestTDs:
                childAnchor = testTD.findChild("a")
                testTitle = childAnchor.getText()
                testLink = ""
                if childAnchor.has_key("href"):
                    testLink = self.baseUrl + childAnchor["href"]
                self.allTests[testTitle] = testLink
            nextAnchors = testSoup.findAll("a", {'href' : nextPageLinkPattern})
            nextPageLink = ""
            for nexta in nextAnchors:
                if nexta.getText() == "Next":
                    nextPageLink = nexta['href'].strip()
                    nextPageLink = self.baseUrl + nextPageLink
                    break
            if nextPageLink == self.baseUrl or nextPageLink == "":
                break
            self.httpHeaders['Referer'] = self.requestUrl
            self.requestUrl = nextPageLink
            moreTestsPageContent = self.getPage(nextPageLink)
        return(self.allTests)


    def _dbOperation(self, query):
        try:
            self.cursor.execute(query)
            self.dbconn.commit()
            # Return last inserted auto_increment id for insert queries.
            if re.search(re.compile(r"^insert\s+", re.IGNORECASE|re.MULTILINE|re.DOTALL), query): 
                return self.cursor.lastrowid
        except:
            print "Error executing query '%s' - %s\n"%(query, sys.exc_info()[1])
            return None
        rows = []
        if re.search(re.compile(r"^select\s+", re.IGNORECASE|re.MULTILINE|re.DOTALL), query):
            rows = self.cursor.fetchall()
        return list(rows)
    

    def getTest(self):
        testLink = self.allTests[self.selectedTest]
        testStartPageContent = self.getPage(testLink)
        soup = BeautifulSoup(testStartPageContent)
        # First, ascertain that we have come to the right page - the page for the test selected.
        h1 = soup.find("h1", {'class' : 'oH1'})
        testHeader = self.selectedTest
        if not h1 or h1.getText().strip() != testHeader: # Check if we are already in the test launch page
            anchorStartTest = soup.find("a", {'class' : 'oBtn oBtnPrimary oBtnLarge'})
            expiryPattern = re.compile(r"This\s+test\s+session\s+is\s+expired", re.IGNORECASE|re.MULTILINE|re.DOTALL)
            if anchorStartTest and anchorStartTest.getText().strip() != "Start Test":
                print "Could not find the test start page... Please check manually if it exists."
                return None
            if not anchorStartTest:
                expirySearch = re.search(expiryPattern, testStartPageContent)
                if expirySearch:
                    print "Your test has expired. Please try at a later date\n"
                    return None
            dummyData = self.getQuestion()
            return self.testObject
        # Populate the 'tests' table with the info pertaining to the test.
        syllabus = ""
        duration = ""
        numQuestions = ""
        self.testObject.setName(testHeader)
        ulSyllabus = soup.find("ul", {'class' : 'oBulletList'})
        if not ulSyllabus:
            print "Could not retrieve syllabus...\n"
        else:
            syllabusList = ulSyllabus.contents
            for syl in syllabusList:
                syl = re.sub(self.__class__.newlinePattern, "", syl.__str__())
                syl = re.sub(self.__class__.htmlTagPattern, " ", syl.__str__())
                if syl == "":
                    continue
                syllabus += syl +  "||"
            syllabus = syllabus[:-3]
        allTHs = soup.findAll("th")
        for th in allTHs:
            thtext = th.getText().strip()
            if thtext == "Duration":
                duration = th.findNext("td").getText().strip()
            elif thtext == "Number of Questions":
                numQuestions = th.findNext("td").getText().strip()
            else:
                continue
        self.testObject.setAttribs(syllabus, duration, numQuestions)
        return self.testObject


    """
    Initializes 'self.testObject' member.
    """
    def getQuestion(self):
        soup = BeautifulSoup(self.currentPageContent)
        # Find the 'Start Test' green coloured button 
        startTestButton = soup.find("a", {'class' : 'oBtn oBtnPrimary oBtnLarge'})
        # Confirm that this is the button we are looking for.
        startTestButtonText = startTestButton.getText().strip()
        if not re.search(re.compile(r"Start\s+Test", re.IGNORECASE|re.MULTILINE|re.DOTALL), startTestButtonText):
            print "Could not find the button to start the test."
            return(None)
        testInstructionsPageLink = startTestButton['href']
        if not re.search(self.__class__.absUrlPattern, testInstructionsPageLink):
            testInstructionsPageLink = self.baseUrl + testInstructionsPageLink
        self.httpHeaders['Referer'] = self.requestUrl
        # Can't use getPage here as 'Host' header changes
        self.requestUrl = testInstructionsPageLink
        self.pageRequest = urllib2.Request(self.requestUrl, None, self.httpHeaders)
        locHeader = ""
        requestUrl = ""
        try:
            pageResponse = self.no_redirect_opener.open(self.pageRequest)
            responseHeaders = pageResponse.info()
            if responseHeaders.has_key('Location'):
                requestUrl = responseHeaders['Location']
                locHeader = requestUrl
                if not re.search(self.__class__.absUrlPattern, responseHeaders['Location']):
                    requestUrl = self.baseUrl + responseHeaders['Location']
                    locHeader = requestUrl
        except:
            responseHeaders = pageResponse.info()
            print "Could not find the redirect URL (Location header from the HTTP response). - %s\n"%self.pageResponse.getcode()
        if not locHeader:
            return None
        try:
            resp = urllib2.urlopen(requestUrl)
            contents = resp.read()
        except:
            resp = None
            print "Could not make the request to '%s' - %s"%(requestUrl, sys.exc_info()[1])
            contents = ""
        expiredPattern = re.compile(r"(Your\s+test\s+has\s+expired\.\s+You\s+cannot\s+retake\s+this\s+test\s+before\s+[^<]+)<", re.IGNORECASE|re.MULTILINE|re.DOTALL)
        expirySearch = re.search(expiredPattern, contents)
        if expirySearch:
            expiryGroups = expirySearch.groups()
            return({'EXPIRY' : expiryGroups[0]})
        # Now get the form that has the submit button that needs to be clicked to actually start the test
        soup = BeautifulSoup(contents)
        testForm = soup.find("form")
        if not testForm or not testForm.has_key("action"):
            # Check this, this might be the new format page for tests on odesk
            newQuestionDataList = [ -1,  None, {} ]
            newQuestionDataList = self._handleNewQuestionFormat(contents)
            return( newQuestionDataList )
        testRequestUrl = testForm['action']
        if not re.search(self.__class__.absUrlPattern, testRequestUrl):
            testRequestUrl = "https://odesk.expertrating.com" + testRequestUrl
        inputTag = testForm.find("input", {'type' : 'hidden', 'name' : 'ii'})
        inputData = ""
        if inputTag:
            inputData = inputTag['value']
        dataDict = {'ii' : inputData}
        postData = urllib.urlencode(dataDict)
        httpHeaders = {}
        httpHeaders['Content-Type'] = "application/x-www-form-urlencoded"
        httpHeaders['Content-Length'] = postData.__len__()
        httpHeaders['Cache-Control'] = "max-age=0"
        httpHeaders['Referer'] = requestUrl
        pageRequest = urllib2.Request(testRequestUrl, postData, httpHeaders)
        try:
            pageResponse = urllib2.urlopen(pageRequest)
        except:
            print "Could not fetch the page with the question - %s\n"%sys.exc_info()[1]
            return []
        questionText = pageResponse.read()
        self.currentPageContent = questionText # We need this in the getNextQuestion() method
        questionDataList = self._parseQuestionPage(questionText)
        result = []
        if questionDataList[0] != -1:
            result = self._fetchAnswerFromDB(questionDataList[1])
            questionDataList.append(result)
        else:
            questionDataList.append(["", "", -1, ""])
        return(questionDataList)
                


    def _handleNewQuestionFormat(self, content):
        f = open("newQuestionFormat.html", "w")
        f.write(content)
        f.close()
        newExpiredPattern = re.compile("This\s+test\s+session\s+is\s+expired\.", re.IGNORECASE | re.MULTILINE | re.DOTALL)
        if re.search(newExpiredPattern, content):
            print "This test session has expired. Please try again later.\n"
            return({'EXPIRY' : "This test session has expired. Please try again at a later date.\n"})
        soup = BeautifulSoup(content)
        form = soup.find("form")
        formAction = ""
        if type(form) == dict and form.has_key("action"):
            formAction = form['action']
        else:
            return (["", -1, {}])
        if not re.search(self.__class__.formAction, formAction):
            formAction = self.baseUrl + formAction
        questionPara = soup.find("p", {'class' : 'oTxtMed'})
        question = ""
        if questionPara:
            questionPara = re.sub(self.__class__.htmlTagPattern, "", questionPara)
        question = questionPara.getText()
        ansOptionsDiv = soup.find("div", {'id' : 'answerOptions'})
        allOptionTags = ansOptionsDiv.findAll("input", {'type' : 'checkbox'})
        if not allOptionTags.__len__() > 0:
            allOptionTags = ansOptionsDiv.findAll("input", {'type' : 'radio'})
        answerStructure = {}
        for optTag in allOptionTags:
            answerTextTag = optTag.findNext("pre")
            answerText = answerTextTag.getText()
            if optTag.has_key("name"):
                answerStructure[optTag["name"]] = answerText
        formUserId = form.find("input", {'name' : 'user_id'})
        formQuestionId = form.find("input", {'name' : 'question_id'})
        questionNumberTag = soup.find("h2", {'class' : 'oH2Low'})
        qNo = questionNumberTag.getText()
        retval = [qNo, question, answerStructure]
        #postData = {'user_id' : formUserId, 'question_id' : formQuestionId, }
        #request = urllib2.Request()
        return(retval)


        
        
    """
    Internal method to parse and retrieve the question and answer options from the tests question pages.
    """
    def _parseQuestionPage(self, questionPageContent):
        soup = BeautifulSoup(questionPageContent)
        questionNumDiv = soup.find("div", {'style' : 'width:200px;float:left'})
        if not questionNumDiv:
            retval = [ -1, None, {} ]
            return retval
        questionNum = questionNumDiv.getText()
        questionTextTD = soup.find("td", {'style' : 'padding-left:4px'})
        questionText = questionTextTD.getText().strip().lower()
        answerOptions = {}
        allAnswerIndices = soup.findAll("div", {'style' : 'width:3%;border:solid 0px red;float:left'})
        for ansIndex in allAnswerIndices:
            if not ansIndex:
                continue
            ansIndexContent = ansIndex.getText().strip()
            ansIndexContent = re.sub(re.compile("\."), "", ansIndexContent)
            ansContentDiv = ansIndex.findNext("div")
            ansContent = ansContentDiv.getText().strip()
            answerOptions[ansIndexContent] = ansContent
        if re.search(re.compile("id=check\d+", re.MULTILINE | re.DOTALL), questionPageContent):
            self.multipleChoiceFlag = True
        else:
            self.multipleChoiceFlag = False
        retval = [questionNum, questionText, answerOptions]
        # So point to note: element 0 is question number, element 1 is question, and element 2 is the answer as a dict.
        return(retval)



    def _fetchAnswerFromDB(self, questionText):
        questionText = re.sub(self.__class__.quotePattern, "~", questionText) # Remember: when we enter data in the database, we need to wipe out all quote characters from the data.
        questionSql = "select testId, answer, questionId, answerString from questions where question = '%s'"%questionText.lower()
        rows = self._dbOperation(questionSql)
        if rows.__len__() == 0:
            questionSql = "select testId from tests where testName='%s'"%self.selectedTest
            rows = self._dbOperation(questionSql)
            if rows.__len__() > 0:
                return [rows[0][0], "", -1] # Database has no data for this question, but the test exists in DB
            else:
                return [-1, "", -1]
        answerOption = ""
        testId = -1
        for row in rows:
            answerOption = row[1]
            testId = row[0]
            questionId = row[2]
            answerString = row[3]
            retList = [testId, answerOption, questionId, answerString]
            self.testExistsInDB = 1
        return(retList) # returns a list


    """
    Fetches the question from the next question page. This also submits the answer to the current question.
    """
    def getNextQuestion(self, questionInfo):
        soup = BeautifulSoup(self.currentPageContent)
        h1 = soup.find("h1")
        if h1 and h1.renderContents() == "Test complete!":
            return(-1)
        contents = self.currentPageContent
        expiredPattern = re.compile(r"(Your\s+test\s+has\s+expired\.\s+You\s+cannot\s+retake\s+this\s+test\s+before\s+[^<]+)<", re.IGNORECASE|re.MULTILINE|re.DOTALL)
        expirySearch = re.search(expiredPattern, contents)
        if expirySearch:
            expiryGroups = expirySearch.groups()
            return({'EXPIRY' : expiryGroups[0]})
        form = soup.find("form", {'name' : 'form1'})
        if not form:
            # Check this, this might be the new format page for tests on odesk
            newQuestionDataList = [ -1,  None, {} ]
            newQuestionDataList = self._handleNewQuestionFormat(contents)
            return( newQuestionDataList ) # Could not find the form in HTML
        submitUrl = form["action"]
        if not re.search(self.__class__.absUrlPattern, submitUrl):
            submitUrl = "https://odesk.expertrating.com/" + submitUrl
        formData = {}
        allHiddenFields = soup.findAll("input", {'type' : 'hidden'})
        self.multipleChoiceFlag = False
        allCheckboxes = soup.findAll("input", {'type' : 'checkbox'})
        if allCheckboxes.__len__() > 0:
            self.multipleChoiceFlag = True
        for hiddenField in allHiddenFields:
            fieldName = ""
            if hiddenField.has_key("name"):
                formData[hiddenField['name']] = ""
            else:
                continue
            if hiddenField.has_key("value"):
                formData[hiddenField['name']] = hiddenField['value']
        if not self.multipleChoiceFlag:
            formData['radio'] = questionInfo[3][1]
        else:
            choices = questionInfo[3][1].split("&")
            if type(choices) == list and choices.__len__() > 0:
                for chc in choices:
                    chnums = chc.split("=")
                    ch1, ch2, ch3, ch4, ch5 = "", "", "", "", ""
                    if chnums.__len__() > 3:
                        ch5 = chnums[4]
                        ch4 = chnums[3]
                        ch3 = chnums[2]
                        ch2 = chnums[1]
                        ch1 = chnums[0]
                    elif chnums.__len__() > 2:
                        ch3 = chnums[2]
                        ch2 = chnums[1]
                        ch1 = chnums[0]
                    elif chnums.__len__() > 1:
                        ch2 = chnums[1]
                        ch1 = chnums[0]
                    else:
                        ch1 = chnums[0]
                    formData[ch1] = ch1
                    formData[ch2] = ch2
                    formData[ch3] = ch3
                    formData[ch4] = ch4
                    formData[ch5] = ch5
        formData['next'] = "Next"
        postData = urllib.urlencode(formData)
        httpHeaders = {}
        httpHeaders['Content-Type'] = "application/x-www-form-urlencoded"
        httpHeaders['Content-Length'] = postData.__len__()
        httpHeaders['Cache-Control'] = "max-age=0"
        httpHeaders['Referer'] = submitUrl
        pageRequest = urllib2.Request(submitUrl, postData, httpHeaders)
        pageResponse = None
        try:
            pageResponse = urllib2.urlopen(pageRequest)
        except:
            print "Could not find the next question. Please try again.\n"
            return([])
        self._addToDB(questionInfo)
        questionText = pageResponse.read()
        self.currentPageContent = questionText # We need this in the getNextQuestion() method
        questionDataList = self._parseQuestionPage(questionText)
        result = []
        if questionDataList[0] != -1:
            result = self._fetchAnswerFromDB(questionDataList[1])
            questionDataList.append(result)
        return(questionDataList)
                

    def _addToDB(self, qInfo):
        question = qInfo[1]
        answer = qInfo[3][1]
        testId = qInfo[3][0]
        testName = self.selectedTest
        lastTestId = testId
        answerString = ""
        if re.search(re.compile("&", re.MULTILINE|re.DOTALL), answer):
            answerParts = answer.split('&')
            for part in answerParts:
                assignments = part.split('=')
                answerString += qInfo[2][assignments[0]] + "|"
            answerString = answerString[:-1]
        else:
            answerString = qInfo[2][answer]
        answerString = re.sub(re.compile(r"[\"\']", re.MULTILINE | re.DOTALL), "~", answerString)
        if type(answer) == list:
            answerString = ''
            for ans in answer:
                answerString += '"' + ans + '",'
            answerString = answerString[:-1]
            answerString = re.sub(re.compile(r"[\"\']", re.MULTILINE | re.DOTALL), "~", answerString)
        # Check if test exists in 'tests' table
        checktests = "select testId from tests where testName='%s'"%testName
        rows = self._dbOperation(checktests)
        if rows.__len__() > 0:
            lastTestId = rows[0][0]
        else: # Add record in 'tests' table
            testName = re.sub(self.__class__.quotePattern, "~", testName)
            self.testObject.syllabus = re.sub(self.__class__.quotePattern, "~", self.testObject.syllabus)
            insertSql = "insert into tests (testName, existsInDb, numQuestions, duration, syllabus, testLink) values ('%s', '%s', '%s', '%s', '%s', '')"%(self.testObject.name, 1, self.testObject.numQuestions, self.testObject.duration, self.testObject.syllabus)
            lastTestId = self._dbOperation(insertSql)
        setSql = ""
        if not self.testExistsInDB:
            question = re.sub(self.__class__.quotePattern, "~", question)
            setSql = "insert into questions (testId, question, answer, answerString) values ('%s', '%s', '%s', '%s')"%(lastTestId, question.lower(), answer, answerString)
        else:
            question = re.sub(self.__class__.quotePattern, "~", question)
            checkQuestionSql = "select answer, answerString from questions where testId=%s and question='%s'"%(lastTestId, question)
            chkQuestion = self._dbOperation(checkQuestionSql)
            if not chkQuestion:
                setSql = "insert into questions (testId, question, answer, answerString) values ('%s', '%s', '%s', '%s')"%(lastTestId, question.lower(), answer, answerString)
            else:
                setSql = "update questions set answerString='%s', answer='%s' where question='%s' and testId='%s'"%(answer, answerString, question.lower(), lastTestId)
        dummy = self._dbOperation(setSql)
    

    # Just check to see if the content has an anchor tag with the text 'Logout' in it.
    def _assertLogin(self): 
       soup = BeautifulSoup(self.currentPageContent)
       allanchors = soup.findAll("a")
       logoutPattern = re.compile(r"Logout", re.IGNORECASE | re.DOTALL | re.MULTILINE)
       for aTag in allanchors:
           aText = aTag.renderContents()
           #print "ASSERT LOGIN: ", aText
           aText = aText.strip(" ")
           if logoutPattern.search(aText):
               print "Successfully logged into " + self.websiteUrl
               return True
       if logoutPattern.search(self.currentPageContent):
           print "Successfully logged into " + self.websiteUrl
           return True
       print "Not sure if login was successful in " + self.websiteUrl
       return False



    def _getCookieFromResponse(cls, lastHttpResponse):
        cookies = ""
        lastResponseHeaders = lastHttpResponse.info()
        responseCookies = lastResponseHeaders.getheaders("Set-Cookie")
        pathCommaPattern = re.compile(r"path=/\s*;?", re.IGNORECASE)
        domainPattern = re.compile(r"Domain=[^;]+;?", re.IGNORECASE)
        expiresPattern = re.compile(r"Expires=[^;]+;?", re.IGNORECASE)
	deletedPattern = re.compile(r"=deleted;", re.IGNORECASE)
        if responseCookies.__len__() >= 1:
            for cookie in responseCookies:
                cookieParts = cookie.split("path=/")
                cookieParts[0] = re.sub(domainPattern, "", cookieParts[0])
                cookieParts[0] = re.sub(expiresPattern, "", cookieParts[0])
		deletedSearch = deletedPattern.search(cookieParts[0])
		if deletedSearch:
		    continue
                cookies += "; " + cookieParts[0]
	    multipleWhiteSpacesPattern = re.compile(r"\s+")
	    cookies = re.sub(multipleWhiteSpacesPattern, " ", cookies)
	    multipleSemicolonsPattern = re.compile(";\s*;")
	    while re.search(multipleSemicolonsPattern, cookies):
                cookies = re.sub(multipleSemicolonsPattern, "; ", cookies)
	    if re.compile("^\s*;").search(cookies):
		cookies = re.sub(re.compile("^\s*;"), "", cookies)
            return(cookies)
	else:
	    return(None)

    _getCookieFromResponse = classmethod(_getCookieFromResponse)


    def populateCookiesDict(self, lastHttpResponse):
        lastResponseHeaders = lastHttpResponse.info()
        responseCookies = lastResponseHeaders.getheaders("Set-Cookie")
        pathCommaPattern = re.compile(r"path=/;", re.IGNORECASE)
        domainPattern = re.compile(r"Domain=.odesk.com", re.IGNORECASE)
        expiresPattern = re.compile(r"Expires=[^;]+;", re.IGNORECASE)
        if responseCookies.__len__() > 1:
            for cookie in responseCookies:
                cookieParts = cookie.split("path=/;")
                cookieParts[0] = re.sub(domainPattern, "", cookieParts[0])
                cookieParts[0] = re.sub(expiresPattern, "", cookieParts[0])
                while re.search(re.compile(r";[^\w]+;", re.MULTILINE | re.DOTALL), cookieParts[0]):
                    cookieParts[0] = re.sub(re.compile(r";[^\w]+;", re.MULTILINE | re.DOTALL), ";", cookieParts[0])
                cookieParts[0] = re.sub(re.compile(r";\s*$"), "", cookieParts[0])
                cookieName, cookieValue = cookieParts[0].split("=")
                if cookieName == "visitor_id":
                    self.visitor_id = cookieValue
                elif cookieName == "":
                    self.leaving_odesk_auto = cookieValue
                self.cookiesDict[cookieName] = cookieValue
        else:
            cookieParts = responseCookies[0].split("path=/;")
            cookieParts[0] = re.sub(domainPattern, "", cookieParts[0])
            cookieParts[0] = re.sub(expiresPattern, "", cookieParts[0])
            cookieName, cookieValue = cookieParts[0].split("=")
            self.cookiesDict[cookieName] = cookieValue
        self.cookiesDict['console_user'] = self.username
        return(self.cookiesDict)


    def _decodeGzippedContent(cls, encoded_content):
        response_stream = StringIO(encoded_content)
        decoded_content = ""
        try:
            gzipper = gzip.GzipFile(fileobj=response_stream)
            decoded_content = gzipper.read()
        except: # Maybe this isn't gzipped content after all....
            decoded_content = encoded_content
        return(decoded_content)

    _decodeGzippedContent = classmethod(_decodeGzippedContent)



    def getPageContent(self):
        if self.pageResponse:
            content = self.pageResponse.read()
            self.currentPageContent = content
            # Remove the line with 'DOCTYPE html PUBLIC' string. It sometimes causes BeautifulSoup to fail in parsing the html
            #self.currentPageContent = re.sub(r"<.*DOCTYPE\s+html\s+PUBLIC[^>]+>", "", content)
            return(self.currentPageContent)
        else:
            return None


    def createCookieStringFromDict(self):
        cookies = ""
        for cookie in self.cookiesDict.keys():
            cookies += "; " + cookie + "=" + self.cookiesDict[cookie]
        cookies = re.sub(re.compile(r"^;", re.MULTILINE | re.DOTALL), "", cookies)
        cookies = re.sub(re.compile(r"^\s+", re.MULTILINE | re.DOTALL), "", cookies)
        cookies = re.sub(self.__class__.multipleWhitespacePattern, " ", cookies)
        return(cookies)



# The 'Test' class is a managed entity to emulate the behaviour of a test on odesk. Users taking test is the
# interaction of the 'User' object and the 'Test' object. The implementation of that activity lies in the
# definition of the 'User' class. A 'Test' object will normally have the following attributes:
# 1. test name/title
# 2. test questions and their respective answer choices (implemented as a  'dict')
# 3. max time interval between 2 consecutive questions in the test object (the actual time will be randomly generated
#    number between 0 and the max value.
# 4. prerequisites required (if any). If there are no prerequisites, this field will be 'None' (which will be the
#    default value as well.

class Test(object):

    def __init__(self, testName=""):
        self.name = testName
        self.syllabus = ""
        self.duration = ""
        self.numQuestions = ""
        self.questionAnswers = {} # Dict containing questions as keys and answers as values. The answers are dicts too, with the answer index as the key and the answer text as the value.


    def getQuestions(self):
        pass


    def setAnswer(self, question, answer):
        pass


    def getAnswer(self, question):
        pass

    def setName(self, name):
        self.name = name
        return(self.name)


    def setAttribs(self, syllabus="", duration="", numQuestions=""):
        self.syllabus = syllabus
        self.duration = duration
        self.numQuestions = numQuestions




class GUIWrapper(object):
    answerIndexSequence = (u'a', u'b', u'c', u'd', u'e', u'f', u'g', u'h', u'i', u'j', u'k', u'l', u'm', u'n', u'o', u'p', u'q', u'r', u's', u't', u'u', u'v', u'w', u'x', u'y', u'z')
    def __init__(self):
        self.bot = OdeskBot()
        self.testsList = []
        self.app = wx.App(True)
        self.frame = wx.Frame(None, wx.ID_ANY, "Odesk Test Master", size=(800,700))
        self.panel = wx.Panel(self.frame, wx.ID_ANY)
        self.noticeBox = wx.StaticText(self.panel, wx.ID_ANY, "Loading... Please DO NOT click on the window until it loads with all the available tests. It might take a few seconds.", pos=(110, 10)) # A place to write out any warnings or status messages.
        self.noticeBox.SetForegroundColour("red")
        self.testListLabel = wx.StaticText(self.panel, wx.ID_ANY, "Select Any Test: ", pos=(20, 30))
        self.testListBox = wx.ListBox(self.panel, wx.ID_ANY, choices=['Select One', ], pos=(110, 30), size=(150, 40))
        self.reanswerCheckBox = wx.CheckBox(self.panel, -1, "Re-answer: ", pos=(370, 30))
        self.takeTestButton = wx.Button(self.panel, wx.ID_ANY, "Start Test", pos=(500, 30))
        self.loadTestMessage = None
        self.expiryMessage = None
        self.questionSubmitButton = None
        self.question = None
        self.questionStaticText = []
        self.rdoButton = []
        self.chkBoxes = []
        self.takeTestButton.Bind(wx.EVT_BUTTON, self.loadTest)
        self.questionInfo = []
        self.frame.Show()


    def login(self, username, password):
        retval = self.bot.login(username, password)
        if not retval:
            print "Could not login with the credentials provided."
            self.loggedin = False
            return None
        self.loggedin = True
        return(self.loggedin)


    def getTests(self):
        testLink = self.bot.getTestLink()
        if not testLink:
            return None
        testsPageContent = self.bot.getPage(testLink)
        self.allTests = self.bot.getAllTests()
        self.testsList = self.allTests.keys()
        if self.testsList.__len__() == 0:
            self.noticeBox = wx.StaticText(self.frame, wx.ID_ANY, "The list of tests could not be extracted from odesk.com.", pos=(110, 30))
            return None
        self.testListBox.InsertItems(self.testsList, 0)
        self.noticeBox.SetLabel("") # Remove the "Loading..." message
        return(self.testsList)


    def submitAnswer(self, evt=None):
        selectedRadioButton = None
        iterctr = 0
        for rdo in range(0, self.rdoButton.__len__()):
            if self.rdoButton[rdo].GetValue():
                selectedRadioButton = self.__class__.answerIndexSequence[iterctr]
                break
            iterctr += 1
        if self.bot.multipleChoiceFlag:
            selectedRadioButton = ""
            iterctr = 0
            for chk in range(0, self.chkBoxes.__len__()):
                if self.chkBoxes[chk].GetValue():
                    selectedRadioButton += self.__class__.answerIndexSequence[iterctr] + "=" + self.__class__.answerIndexSequence[iterctr] + "&"
                iterctr += 1
            selectedRadioButton = selectedRadioButton[:-1] # Remove the last ampersand character
        try:
            self.questionInfo[3][1] = selectedRadioButton
        except IndexError:
            print "Completed test.\n\n"
            return(1)
        questionInfo = self.bot.getNextQuestion(self.questionInfo)
        if questionInfo == -1:
            print "The test is complete.\n"
            return(-1)
        if not questionInfo[0]: # Didn't find a question on the page. Probably there are no more questions and the test is complete
            return None
        self.questionInfo = questionInfo
        if type(questionInfo) == dict and questionInfo.has_key('EXPIRY'):
            print "Your test '%s' seems to have expired.\n"%self.bot.selectedTest
            return (None)
        elif not questionInfo:
            print "Could not find the question.\n"
            return(None)
        # if questionInfo[3][2] equals -1, then this question doesn't exist in the DB. 
        if questionInfo[3][2] == -1 or self.bot.reanswer: # We need to display this to the user
            self.showQuestion(questionInfo)
        else: # Else if the answer to the question exists in the database, then simply submit the answer.
            iterctr = 0
            for rdo in range(0, self.rdoButton.__len__()):
                if self.questionInfo[3][1] == self.__class__.answerIndexSequence[iterctr]:
                    self.rdoButton[rdo].SetValue(True)
                    break
                iterctr += 1
            if self.bot.multipleChoiceFlag:
                selectedBoxes = selectedRadioButton.split("&")
                for  chk in range(0, self.chkBoxes.__len__()):
                    for selbox in selectedBoxes:
                        selpart1, selpart2 = selbox.split("=")
                    if self.chkBoxes[chk] == selpart2:
                        self.chkBoxes[chk].SetValue(True)
            self.submitAnswer(evt)
        return None


    def breakString(cls, str):
        pass
    
    breakString = classmethod(breakString)


    def showQuestion(self, questionInfo):
        # Break the string questionInfo[1] into smaller parts such that no part exceeds 80 characters
        # questionInfo[1] = self.__class__.breakString(questionInfo[1])
        questionDisplayableText = questionInfo[0] + "\n\n" + questionInfo[1] + "\n\n"
        questionDisplayableText = re.sub(re.compile(r"<br\s*\/?>"), "\n", questionDisplayableText)
        questionDisplayableText = re.sub(re.compile(r"&nbsp;"), "  ", questionDisplayableText)
        questionInfoTextPartsMain = questionInfo[0].split(".")
        if questionInfoTextPartsMain.__len__() == 1:
            questionInfoTextPartsMain[0] = questionInfoTextPartsMain[0].capitalize()
        for i in range(0, questionInfoTextPartsMain.__len__() - 1):
            questionInfoTextPartsMain[i] = questionInfoTextPartsMain[i].capitalize()
            questionInfoTextParts[i] = questionInfoTextPartsMain[i].strip()
        questionInfoTextPartsMain = ". ".join(questionInfoTextPartsMain)
        questionInfo[0] = questionInfoTextPartsMain
        questionInfoTextParts = questionInfo[1].split(".")
        if questionInfoTextParts.__len__() == 1:
            questionInfoTextParts[0] = questionInfoTextParts[0].capitalize()
        for i in range(0, questionInfoTextParts.__len__() - 1):
            questionInfoTextParts[i] = questionInfoTextParts[i].capitalize()
            questionInfoTextParts[i] = questionInfoTextParts[i].strip()
        questionInfoTextParts = ". ".join(questionInfoTextParts)
        questionInfo[1] = questionInfoTextParts
        if self.question:
            self.question.Destroy()
        self.question = wx.StaticText(self.panel, wx.ID_ANY, questionDisplayableText, pos=(20, 150))
        self.question.Wrap(700)
        if self.questionStaticText and self.questionStaticText.__len__() > 0:
            questionStaticTestLength = self.questionStaticText.__len__()
            for ctr in range(0, questionStaticTestLength):
                self.questionStaticText[ctr].Destroy()
        #if not self.bot.multipleChoiceFlag:
        if self.rdoButton and self.rdoButton.__len__() > 0:
            rdoButtonLength = self.rdoButton.__len__()
            for ctr in range(0, rdoButtonLength):
                self.rdoButton[ctr].Destroy() # Remove previous question's radio buttons.
        #else:
        if self.chkBoxes and self.chkBoxes.__len__() > 0:
            chkBoxesLength = self.chkBoxes.__len__()
            for ctr in range(0, chkBoxesLength):
                self.chkBoxes[ctr].Destroy()
        self.questionStaticText = []
        self.rdoButton = []
        self.chkBoxes = []
        radctr = 0
        incr = 30
        offset = 200
        indexSequence = questionInfo[2].keys()
        indexSequence.sort()
        maxQuestionDisplayableTextLength = 20 * (indexSequence[0] + ".\t" + questionInfo[2][indexSequence[0]]).__len__()
        for ansIndex in indexSequence:
            if maxQuestionDisplayableTextLength < 20 * (ansIndex + ".\t" + questionInfo[2][ansIndex]).__len__():
                maxQuestionDisplayableTextLength = 20 * (ansIndex + ".\t" + questionInfo[2][ansIndex]).__len__()
        for ansIndex in indexSequence:
            height = (radctr+1)*incr
            questionDisplayableText =  ansIndex + ".\t" + questionInfo[2][ansIndex]
            questionDisplayableText = re.sub(re.compile(r"<br\s*\/?>"), "\n", questionDisplayableText)
            questionDisplayableText = re.sub(re.compile(r"&nbsp;"), "  ", questionDisplayableText)
            height = offset + height
            questionDisplayableTextLength = questionDisplayableText.__len__() * 20
            answerOptionItem = wx.StaticText(self.panel, wx.ID_ANY, questionDisplayableText, pos=(20, height), size=(700, 20))
            answerOptionItem.Wrap(600)
            self.questionStaticText.append(answerOptionItem)
            if not self.bot.multipleChoiceFlag:
                # Create new Radio Buttons for this question's options
                answerRadioOption = wx.RadioButton(self.panel, wx.ID_ANY, pos=(800, height))
                self.rdoButton.append(answerRadioOption)
                radctr += 1
            else:
                answerCheckboxOption = wx.CheckBox(self.panel, wx.ID_ANY, "", pos=(800, height))
                self.chkBoxes.append(answerCheckboxOption)
                radctr += 1
        self.answerSubmitButton = wx.Button(self.panel, wx.ID_ANY, "Submit and Continue", pos=(30, 420))
        self.answerSubmitButton.Bind(wx.EVT_BUTTON, self.submitAnswer)
        self.frame.Show()

    

    def loadTest(self, evt):
        selectedTestIndex = self.testListBox.GetSelection()
        reanswerStatus = False
        reanswerStatus = self.reanswerCheckBox.GetValue()
        self.bot.selectedTest = self.testsList[selectedTestIndex].strip()
        if reanswerStatus:
            self.bot.reanswer = 1
        if self.loadTestMessage:
            self.loadTestMessage.SetLabel("")
        if self.expiryMessage:
            self.expiryMessage.Destroy()
        self.loadTestMessage = wx.StaticText(self.panel, wx.ID_ANY, "Loading '%s'... "%(self.bot.selectedTest), pos=(20, 120))
        self.loadTestMessage.SetForegroundColour("blue")
        self.bot.testObject = self.bot.getTest()
        questionInfo = self.bot.getQuestion()
        self.questionInfo = questionInfo
        if type(questionInfo) == dict and questionInfo.has_key('EXPIRY'):
            self.expiryMessage = wx.StaticText(self.panel, wx.ID_ANY, "Your test '%s' seems to have expired.\n"%self.bot.selectedTest, pos=(20, 120))
            self.expiryMessage.SetForegroundColour("red")
            return (None)
        elif not questionInfo:
            self.expiryMessage = wx.StaticText(self.panel, wx.ID_ANY,  "Could not find the question.\n", pos=(20, 120))
            self.expiryMessage.SetForegroundColour("red")
            return(None)
        # if questionInfo[3][2] equals -1, then this question doesn't exist in the DB. 
        if questionInfo[3][2] == -1 or self.bot.reanswer: # We need to display this to the user
            self.showQuestion(questionInfo)
        else: # Else if the answer to the question exists in the database, then simply submit the answer.
            iterctr = 0
            if not self.bot.multipleChoiceFlag:
                for rdo in range(0, self.rdoButton.__len__() - 1):
                    if self.questionInfo[3][1] == self.__class__.answerIndexSequence[iterctr]:
                        self.rdoButton[rdo].SetValue(True)
                        break
                    iterctr += 1
                self.submitAnswer()
            else: # Read from the checkbox interface.
                selectedChoices = []
                for chkb in range(0, self.chkBoxes.__len__()):
                    selectedListOfChkBoxes = self.questionInfo[3][1]
                    for selectedChkBox in selectedListOfChkBoxes:
                         if selectedChkBox.value() == self.__class__.answerIndexSequence[iterctr]:
                             self.chkBoxes[chkb].SetValue(True)
                    break
                iterctr += 1
                self.submitAnswer()
        self.frame.Show()
        return None



"""
Derived out of 'Thread' class in 'threading' module
"""
class odeskThread(Thread):
    def __init__(self, guiObject, threadId, threadName, threadCounter, username, password):
        Thread.__init__(self)
        self.threadId = threadId
        self.threadName = threadName
        self.threadCounter = threadCounter
        self.guiObject = guiObject
        self.username = username
        self.password = password


    def run(self):
        print "Starting " + self.threadName + "...\n"
        #loggedin = self.guiObject.login("lysander_stark", "spmprx13")
        #loggedin = self.guiObject.login("sherlock_holmes6", "spmprx13")
        loggedin = self.guiObject.login(self.username, self.password)
        if not loggedin:
            print "Could not login into odesk.\n"
            sys.exit()
        alltests = self.guiObject.getTests()





if __name__ == "__main__":
    if sys.argv.__len__() < 3:
        print "Please enter your username and password to run this app.\n"
        sys.exit()
    username = sys.argv[1]
    password = sys.argv[2]
    gui = GUIWrapper()
    threadObject = odeskThread(gui, 1, "backgroundOps", 1, username, password)
    threadObject.start()
    gui.app.MainLoop()

 
