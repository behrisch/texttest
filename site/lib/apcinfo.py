import plugins, os, re, string, math, exceptions, optimization, performance, time, copy, apc, sys
from testmodel import BadConfigError

try:
    import HTMLgen, barchart
except:
    raise BadConfigError, "Python modules HTMLgen and/or barchart not found. Try adding /users/johani/pythonpackages/HTMLgen to your PYTHONPATH."

class CarmenDocument(HTMLgen.SeriesDocument):
    def header(self):
        """Generate the standard header markups.
        """
        # HEADER SECTION - overload this if you don't like mine.
        s = []
        if self.banner:
            bannertype = type(self.banner)
            if bannertype in (HTMLgen.TupleType, HTMLgen.StringType):
                s.append(str(HTMLgen.Center(HTMLgen.Image(self.banner, border=0))) + '<BR>\n')
            elif bannertype == HTMLgen.InstanceType:
                s.append(str(self.banner) + '<BR>\n')
            else:
                raise TypeError, 'banner must be either a tuple, instance, or string.'
        if self.place_nav_buttons:
            s.append(self.nav_buttons())
        s.append('<HR>\n\n')
        return string.join(s, '')
    def footer(self):
        """Generate the standard footer markups.
        """
        # FOOTER SECTION - overload this if you don't like mine.
        t = time.localtime(time.time())
        #self.datetime = time.strftime("%c %Z", t)    #not available in JPython
        self.datetime = time.asctime(t)
        #self.date = time.strftime("%A %B %d, %Y", t)
        x = string.split(self.datetime)
        self.date = x[0] + ' ' + x[1] + ' ' + x[2] + ', ' + x[4]
        s =  ['\n<P><HR>\n']
        if self.place_nav_buttons:
            s.append(self.nav_buttons())
        s.append('\n<FONT SIZE="-1"><P>Copyright &#169 %s<BR>All Rights Reserved<BR>\n' \
            % self.author)
        s.append('\nComments to author: ' + str(HTMLgen.MailTo(self.email)) )
        s.append('<br>\nGenerated: %s <BR>' % self.datetime) # can use self.datetime here instead
        s.append('<hr>\n</FONT>')
        return string.join(s, '')

# We extend this class in order to be able to use more than 6 colors....
class CarmenStackedBarChart(barchart.StackedBarChart):
    def initialize(self):
        barchart.StackedBarChart.initialize(self)
        self.colors = ('blue','red','yellow','purple','orange','green','black')
        barchart.barfiles['black'] = '../image/bar-black.gif'

class BarChart:
    def __init__(self, entries):
        self.entries = entries
        
    def doMeans(self, datalist, groupname, linkgroup = None):
        if linkgroup:
            meanslink = [ HTMLgen.Href(linkgroup, groupname) ]
        means = [ groupname ]

        for keys in self.entries:
            means.append(datalist.mean(keys))
            if linkgroup:
                meanslink.append(datalist.mean(keys))
        if linkgroup:
            return means, meanslink
        else:
            return means

    def createBarChartMeans(self, chart, groupname, glob = None, linkgroupglob = None):
        means, meansglob = self.doMeans(chart.datalist, groupname, linkgroupglob)
        chart.datalist.load_tuple(tuple(means))
        if glob:
            glob.datalist.load_tuple(tuple(meansglob))
        
    def createBarChartMeansRelAbs(self, charts, groupname, globrel = None, linkgroupglob = None):
        chartabs, chartrel = charts

        means, meansglob = self.doMeans(chartrel.datalist, groupname, linkgroupglob)
        chartrel.datalist.load_tuple(tuple(means))
        if globrel:
            globrel.datalist.load_tuple(tuple(meansglob))
        
        means = self.doMeans(chartabs.datalist, groupname)
        chartabs.datalist.load_tuple(tuple(means))

    def createBC(self, title):
        chart = CarmenStackedBarChart()
        chart.title = title
        chart.datalist = barchart.DataList()
        chart.datalist.segment_names = tuple(self.entries)
        return chart

    def createRelAbsBC(self):
        chartabs = self.createBC("Absolute times")
        chartrel = self.createBC("Relative times")
        return chartabs, chartrel

    def fillData(self, vals, data):
        data.load_tuple(tuple(vals))
        
    def fillDataRelAbs(self, vals, total, data):
        dataabs, datarel = data
        dataabs.load_tuple(tuple(vals))
        relvals = []
        for val in vals:
            if len(relvals) > 0:
                relvals.append(float(val)/total)
            else:
                relvals.append(val)
        datarel.load_tuple(tuple(relvals))

class AnalyzeLProfData:
    def __init__(self):
        self.interestingFunctions = ["CGSUB::pricing",
                                     "CO_PAQS::optimize",
                                     "CGSUB::fix_variables",
                                     "CGSUB::unfix_variables",
                                     "CGSUB::feasible",
                                     "apc_setup"]
        self.raveFunctions = ["CRCExecuteAllRules",
                              "CRCComputeValueArgs",
                              "CRCSetRotation",
                              "CRCModifyRotation",
                              "CRCCollectInfo",
                              "CRCApplicationRetrieveValue"]
        self.hatedFunctions = {}
        self.numMeans = 0

        self.reFlat = re.compile(r'[0-9]{1,2}\.[0-9]{1} *[0-9]{1,2}\.[0-9]{1}.*')
        self.reCall = re.compile(r'-{1} *[0-9]{1,3}- *[0-9]{1,2}\.[0-9]{1} *[0-9]{1,2}\.[0-9]{1}.*')

    def doFlatProf(self, line, fcns):
         profLine = self.reFlat.search(line)
         if profLine:
            data = profLine.group().split()
            funcName = data[2]
            funcPerc = float(data[0])
            if len(self.top20) < 20:
                self.top20.append((funcName, funcPerc))
                if fcns.has_key(funcName):
                    fcns[funcName] += funcPerc
                else:
                    fcns[funcName] = funcPerc
                
    def doCallGraph(self, line):
        profLine = self.reCall.search(line)
        if profLine:
            data = profLine.group()
            minus = data.rfind("-",0,10)
            data = data[minus+1:].split()
            funcName = data[2]
            funcPerc = float(data[0])
            try:
                ind = self.interestingFunctions.index(funcName)
                #print funcName, funcPerc
                self.sum += funcPerc
            except ValueError:
                pass
            try:
                ind = self.raveFunctions.index(funcName)
                #print funcName, funcPerc
                self.rave[funcName] = funcPerc
                self.sumRave += funcPerc
            except ValueError:
                pass

    def analyze(self, lprofFileName, data):
        self.flat = None
        self.call = None
        self.top20 = []
        self.sum = 0
        self.sumRave = 0
        self.rave = {}
        file = open(lprofFileName)
        for line in file.readlines():
            if line.find("Flat profile") != -1:
                self.flat = 1
                self.call = None
                continue
            if line.find("Call graph") != -1:
                self.flat = None
                self.call = 1
                continue
            if self.flat:
                self.doFlatProf(line, data["fcns"])
            if self.call:
                self.doCallGraph(line)
        data["count"] += 1
        return self.rave
                
    def profileBarChart(self, fcns, div = None):
        rank = fcns.keys()
        rank.sort(lambda x, y: cmp(int(100*fcns[x]), int(100*fcns[y])))
        rank.reverse()

        chart = barchart.BarChart()
        chart.title = "Top 10 most time consuming functions."
        chart.datalist = barchart.DataList()

        count = 0
        for line in rank:
            if div:
                val = fcns[line] / self.numMeans
            else:
                val = fcns[line]
            chart.datalist.load_tuple((line, val))
            count += 1
            if count > 10:
                break
        return chart
        
    def doMeans(self, data):
        count = data["count"]
        for fcn in data["fcns"].keys():
            data["fcns"][fcn] /= count
            if self.hatedFunctions.has_key(fcn):
                self.hatedFunctions[fcn] += data["fcns"][fcn]
            else:
                self.hatedFunctions[fcn] = data["fcns"][fcn]
        self.numMeans += 1

        return self.profileBarChart(data["fcns"])


class GenHTML(plugins.Action):
    def __init__(self, args = None):
        htmlDir = None
        if args:
            htmlDir = args[0]
        self.htmlDir = "/carm/documents/Development/Optimization/Testing"
        if htmlDir and os.path.isdir(htmlDir):
            self.htmlDir = htmlDir
        else:
            print "No html dir specified/the dir does not exist, uses", self.htmlDir

        self.profilesDir = "/carm/documents/Development/Optimization/APC/profiles"
        self.profilesDirAsHtml = "http://www-oint.carmen.se/Development/Optimization/APC/profiles"
        self.indexFile = self.htmlDir + os.sep + "testindex.html"
        
    def setUpApplication(self, app):
        # Override some setting with what's specified in the config file.
        dict = app.getConfigValue("apcinfo")
        if dict.has_key("profilesDir"):
            self.profilesDir = dict["profilesDir"]
        if dict.has_key("profilesDirAsHtml"):
            self.profilesDirAsHtml = dict["profilesDirAsHtml"]
        
        self.RCFile = app.dircache.pathName("apcinfo.rc")

        self.definingValues = [ "Network generation time", "Generation time", "Coordination time", "DH post processing" ]
        self.interestingValues = ["Conn fixing time", "OC to DH time"]
        #self.tsValues = self.definingValues + self.interestingValues + ["Other time"]
        self.tsValues = [ "Network gen", "Generation", "Coordination", "DH post", "Conn fix", "OC->DH", "Other" ]
        self.interestingParameters = [ "add_tight_deadheads_active_copies",
                                       "add_tight_deadheads_other",
                                       "add_all_passive_copies_of_active_flights",
                                       "add_all_other_local_plan_deadheads",
                                       "search_for_double_deadheads",
                                       "optimize_deadhead_chains",
                                       "use_ground_transport",
                                       "use_long_haul_preprocess",
                                       "search_oag_deadheads",
                                       "allow_oag_deadheads"]
        self.timeSpentBC = BarChart(self.tsValues)
        
        # The global chart for relative times.
        self.chartrelglob = CarmenStackedBarChart()
        self.chartrelglob.title = "Relative times"
        self.chartrelglob.datalist = barchart.DataList()
        self.chartrelglob.datalist.segment_names = tuple(self.tsValues)

        # Variation
        self.variationChart = barchart.BarChart()
        self.variationChart.datalist = barchart.DataList()
        self.variationChart.thresholds = (5, 10)
        self.variationChart.title = "Variation in per mil"
        
        # Rule failures
        self.ruleFailureChart = barchart.BarChart()
        self.ruleFailureChart.datalist = barchart.DataList()
        self.ruleFailureChart.thresholds = (20, 60)
        self.ruleFailureChart.title = "Rule failures in percent"

        # Table with interesting parameters
        self.interParamsTable = HTMLgen.Table()
        self.interParamsTable.heading = copy.deepcopy(self.interestingParameters)
        self.interParamsTable.heading.insert(0, "KPI group")
        self.interParamsTable.body = []

        self.clientSuiteList = {}
        self.nonClientSuiteList = []
        self.numberOfTests = 0
        self.totalCPUtime = 0
        
        self.kpiGroupForTest = {}
        self.kpiGroups = []
        self.kpiGroupsList = {}
        self.clientname = None

        self.suitePages = {}

        # Profiling data.
        self.lprof = AnalyzeLProfData()
        self.raveBC = BarChart(self.lprof.raveFunctions) # Extract RAVE functions from profiling data.
        self.profilingGroups = HTMLgen.Container()
        self.profilingGroups.append(HTMLgen.Text("Used groups: "))

        # Global chart for relative RAVE times.
        self.chartRaveglob = CarmenStackedBarChart()
        self.chartRaveglob.title = "Relative time spent by RAVE in APC"
        self.chartRaveglob.datalist = barchart.DataList()
        self.chartRaveglob.datalist.segment_names = tuple(self.lprof.raveFunctions)

    def createTable(self, suites):
        table = HTMLgen.TableLite(border = 1, width = "100%")
        table.append(HTMLgen.TR() + [HTMLgen.TH("Suite", rowspan = 2), HTMLgen.TH("KPI group/test", rowspan = 2), HTMLgen.TH("Description", colspan= 3 ), HTMLgen.TH("Created", rowspan = 2), HTMLgen.TH("Last update", rowspan = 2)])
        table.append(HTMLgen.TR() + [HTMLgen.TH("COC/CAB"), HTMLgen.TH("Subproblem"), HTMLgen.TH("Daily/Weekly/Dated")])
        numItems = 0
        for suite in suites:
            suitename = suite["suitename"]
            suitepagename = suitename + ".html"
            suitedata = []
            for group in suite["group"].keys():
                grouplink = suitepagename + "#" + group
                if group == "common":
                    for test in suite["group"][group]["table"]:
                        testname = test[0]
                        period_start, timeper = suite["groupsandtests"][testname]["description"]
                        suitedata.append((HTMLgen.Href(grouplink, testname), "N/A", "N/A", timeper, period_start, test[-1])) 
                else:
                    grouptable = suite["group"][group]["table"]
                    firsttestingroup = grouptable[0]
                    period_start, timeper = suite["groupsandtests"][group]["description"]
                    suitedata.append((HTMLgen.Href(grouplink, HTMLgen.Strong(group + " (" + str(len(grouptable)) + ")")), "N/A", "N/A", timeper, period_start, firsttestingroup[-1]))
            isFirst = True
            for item, coccab,subprob, dwd, perstart, lastrun in suitedata:
                row = []
                if  isFirst:
                    isFirst = False
                    row.append(HTMLgen.TD(HTMLgen.Href(suitepagename, suitename), rowspan = len(suitedata), bgcolor = "White"))
                row += [HTMLgen.TD(item), HTMLgen.TD(coccab), HTMLgen.TD(subprob), HTMLgen.TD(dwd), HTMLgen.TD(perstart), HTMLgen.TD(lastrun)]
                if numItems % 2:
                    bgCol = "GhostWhite"
                else:
                    bgCol = "White"                
                table.append(HTMLgen.TR(bgcolor = bgCol) + row)
                numItems += 1
        return table

    def writeIndexPage(self):
        self.idoc = CarmenDocument(self.RCFile)
        clients = self.clientSuiteList.keys()
        clients.sort()
        clientcontainer = HTMLgen.Container()
        for clientname in clients:
            clientcontainer.append(HTMLgen.Href("#" + clientname, clientname))
        self.idoc.append(HTMLgen.Heading(2,clientcontainer))
        self.idoc.append(HTMLgen.HR())
        for clientname in clients:
            suites = self.clientSuiteList[clientname]
            self.idoc.append(HTMLgen.Name(clientname, HTMLgen.Heading(1, clientname)))
            self.idoc.append(self.createTable(suites))
        self.idoc.append(HTMLgen.Heading(1, "Non-client tests"))
        self.idoc.append(self.createTable(self.nonClientSuiteList))

        self.idoc.append(HTMLgen.Text("Number of tests: " + str(self.numberOfTests)))
        self.idoc.append(HTMLgen.BR())
        self.idoc.append(HTMLgen.Text("Total CPU time:  " + str("%.1f" % (self.totalCPUtime/60)) + "h"))
        self.idoc.write(self.indexFile)

    def writeBasicSummaryPage(self, title, pagename, pagedata, introtext = None, explaintext = None):
        doc = CarmenDocument(self.RCFile)
        doc.title = title
        if introtext:
            introtextFile = os.path.join(self.htmlDir, introtext)
            if os.path.isfile(introtextFile):
                doc.append_file(introtextFile)
                
        doc.append(pagedata)

        if explaintext:
            explaintextFile = os.path.join(self.htmlDir, explaintext)
            if os.path.isfile(explaintextFile):
                doc.append_file(explaintextFile)
        doc.write(os.path.join(self.htmlDir, pagename))
    def createSummaryPages(self):
        # Write the time spent page.
        totalMeans = self.timeSpentBC.doMeans(self.chartrelglob.datalist, "ALL")
        self.chartrelglob.datalist.load_tuple(tuple(totalMeans))

        cont = HTMLgen.Container()
        cont.append(self.chartrelglob)
        cont.append(HTMLgen.Paragraph())
        cont.append(HTMLgen.Href('testindex.html', 'To test set page'))
        self.writeBasicSummaryPage("Where does APC spend time?", "timespent.html", \
                                   cont, 'timespent-intro-txt.html', 'timespent-expl-txt.html')
                                   

        # Write the Rave spent page.
        totalMeans = self.raveBC.doMeans(self.chartRaveglob.datalist, "ALL")
        self.chartRaveglob.datalist.load_tuple(tuple(totalMeans))

        cont = HTMLgen.Container()
        cont.append(self.profilingGroups)
        cont.append(self.chartRaveglob)
        cont.append(HTMLgen.Paragraph())
        cont.append(HTMLgen.Href('testindex.html', 'To test set page'))
        self.writeBasicSummaryPage("Relative time spent by RAVE in APC", "ravespent.html", cont)

        # Write variation page
        if len(self.variationChart.datalist):
            self.writeBasicSummaryPage("Cost variation for different groups", "variation.html", \
                                       self.variationChart, 'variation-intro-txt.html')

        # Write rule failure page
        if len(self.ruleFailureChart.datalist):
            self.writeBasicSummaryPage("Rule failures for different groups", "rulefailures.html", \
                                       self.ruleFailureChart, 'rulefailures-intro-txt.html')

        # Write interesting parameters page
        if self.interParamsTable.body:
            self.writeBasicSummaryPage("Deadhead parameter settings", "deadheadparams.html", \
                                       self.interParamsTable)

        # Write most hated page.
        if self.lprof.hatedFunctions:
            cont = HTMLgen.Container()
            cont.append(self.profilingGroups)
            cont.append(self.lprof.profileBarChart(self.lprof.hatedFunctions, 1))
            self.writeBasicSummaryPage("The 10 most time consuming functions in APC", "hatedfcns.html", \
                                       cont) 
            
    def __del__(self):
        # Don't write anything for 0 tests, not interesting
        if self.numberOfTests == 0:
            return
        
        # Write the main page.
        self.writeIndexPage()

        # Write suite pages.                       
        for suites in self.suitePages.keys():
            self.buildSuitePage(self.suitePages[suites])

        self.createSummaryPages()
        
    def __repr__(self):
        return "Generating HTML info for"

    # Builds the actual content for the group.
    def buildSuitePage(self, suitePage):
        page = CarmenDocument(self.RCFile)
        suitename = suitePage["suitename"]
        page.append(HTMLgen.Center(HTMLgen.Heading(1, suitename)))
        for groups in suitePage["group"].keys():
            page.append(HTMLgen.HR())
            page.append(HTMLgen.Name(groups))
            if groups == "common":
                page.append(HTMLgen.Heading(2, "Non-grouped tests"))
            else:
                page.append(HTMLgen.Heading(2, "KPI group " + groups))

            if suitePage["group"][groups]["info"]:
                page.append(HTMLgen.Heading(3,"Short summary"))
                page.append(suitePage["group"][groups]["info"])

            if not groups == "common":
                linkToTest = HTMLgen.Href(suitename + ".html" + "#" + groups, groups)
                
                # append cost_spread to variationChart
                cost_spread, meanvar = self.calcCostAndPerfMeanAndVariation(suitePage["group"][groups]["table"])
                if cost_spread*1000 <= 20:
                    self.variationChart.datalist.load_tuple((linkToTest, cost_spread*1000))
                
                ruleFailureAvg = suitePage["group"][groups]["rulecheckfailureavg"]/suitePage["group"][groups]["numtests"]
                self.ruleFailureChart.datalist.load_tuple((linkToTest, 100*ruleFailureAvg))
                # Insert interesting params into table.
                row = [ linkToTest ]
                for params in self.interestingParameters:
                    if suitePage["group"][groups]["interestingParameters"].has_key(params):
                        row.append(suitePage["group"][groups]["interestingParameters"][params])
                    else:
                        row.append("-")
                self.interParamsTable.body.append(row)
            table = HTMLgen.Table()
            table.body = suitePage["group"][groups]["table"]
            table.heading = ["Test", "Cost", "Perf. (min)", "Mem (MB)", "Uncov", "Overcov", "Illegal", "Rule checks/failures", "Date"]
            page.append(table)
            if not groups == "common":
                page.append(meanvar)

            if suitePage["group"][groups]["barcharts"]:
                charts = chartabs, chartrel = suitePage["group"][groups]["barcharts"]
                if not groups == "common":
                    self.timeSpentBC.createBarChartMeansRelAbs(charts, groups, self.chartrelglob, suitename + ".html" + "#" + groups)
                page.append(chartrel)
                page.append(chartabs)

            if suitePage["group"][groups]["profiling"]:
                data = suitePage["group"][groups]["profiling"]
                chart = self.lprof.doMeans(data)
                
                page.append(HTMLgen.Heading(3,"Profiling"))
                page.append(chart)
                page.append(HTMLgen.Paragraph())
                if not groups == "common":
                    self.raveBC.createBarChartMeans(data["ravebc"], groups, self.chartRaveglob, suitename + ".html" + "#" + groups)
                page.append(data["ravebc"])
                page.append(HTMLgen.Paragraph())
                page.append("Used tests for profiling results: ")
                page.append(self.findProfilingGraph(suitename, data["tests"]))
                self.profilingGroups.append(HTMLgen.Href(suitename + ".html" + "#" + groups, HTMLgen.Text(groups)))
        page.title = "APC test suite user " + suitename
        page.write(self.htmlDir + os.sep + suitename + ".html")

    def findProfilingGraph(self, suite, tests):
        profTests = HTMLgen.Container()
        if not os.path.isdir(self.profilesDir):
            return profTests
        filesInProfileDir = os.listdir(self.profilesDir)
        for test in tests:
            foundProfile = 0
            lookForFileStartingWith = suite + "__" + test + "_t5_prof.ps"
            for file in filesInProfileDir:
                if file.find(lookForFileStartingWith) != -1:
                    foundProfile = 1
                    break
            if foundProfile:
                profTests.append(HTMLgen.Href(self.profilesDirAsHtml + os.sep + file, HTMLgen.Text(test)))
            else:
                profTests.append(HTMLgen.Text(test))
        return profTests

    def calcCostAndPerfMeanAndVariation(self, table):
        cost = []
        cost_mean = 0
        perf = []
        perf_mean = 0
        num = 0
        for tests in table:
            cost.append(tests[1])
            cost_mean += cost[-1]
            perf.append(tests[2])
            perf_mean += perf[-1]
            
            if num == 0:
                cost_max = cost_min = cost[-1]
                perf_max = perf_min = perf[-1]
            else:
                if cost[-1] > cost_max:
                    cost_max = cost[-1]
                if cost[-1] < cost_min:
                    cost_min = cost[-1]
                if perf[-1] > perf_max:
                    perf_max = perf[-1]
                if perf[-1] < perf_min:
                    perf_min = perf[-1]
            num += 1
        cost_mean /= num
        perf_mean /= num

        cost_spread = float(cost_max)/float(cost_min) - 1
        try:
            perf_spread = float(perf_max)/float(perf_min) - 1
        except exceptions.ZeroDivisionError:
            perf_spread = 0
        
        cost_var = 0
        perf_var = 0
        num = 0
        for tests in table:
            tmp = cost[num] - cost_mean
            cost_var += tmp*tmp
            
            tmp = perf[num] - perf_mean
            perf_var += tmp*tmp
            num +=1
        cost_var = math.sqrt(cost_var/num)/cost_mean
        try:
            perf_var = math.sqrt(perf_var/num)/perf_mean
        except exceptions.ZeroDivisionError:
            perf_var = 0

        meanvar = HTMLgen.Paragraph()
        meanvar.append("Cost, mean: " + str(int(cost_mean)) + ", scaled std. dev: " + str("%.4f" % cost_var) + ", spread: " + str("%.4f" % (100*cost_spread)) + "%")
        meanvar.append(HTMLgen.BR())
        meanvar.append("Performance, mean: " + str(int(perf_mean)) + ", scaled std. dev: " + str("%.4f" % perf_var) + ", spread: " + str("%.4f" % (100*perf_spread)) + "%")
        return cost_spread, meanvar
        
    def extractTestInfo(self, group, test):
        # TODO
        if test.app.name == "cas":
            return "Something for Kruuse", "Oh yes"
        
        subplanDir = test.app._getSubPlanDirName(test)
        info = HTMLgen.Paragraph()

        # Info from status file
        logFile = test.getFileName(test.app.getConfigValue("log_file"))
        optRun = optimization.OptimizationRun(test.app, ["legs\.", optimization.periodEntryName] ,[] ,logFile)
        periodStart = None
        timeper = None
        if optRun.solutions:
            input = optRun.solutions[0]
            period_start, period_end = input[optimization.periodEntryName]
            date_start = time.mktime(time.strptime(period_start.strip(), "%Y%m%d"))
            date_end = time.mktime(time.strptime(period_end.strip(), "%Y%m%d"))

            if date_start == date_end:
                info.append("Daily")
                timeper = "Daily"
            elif date_end == date_start + 6*1440*60:
                info.append("Weekly")
                timeper = "Weekly"
            else:
                info.append("Dated (" + str(int((date_end-date_start)/1440/60) + 1) + " days)")
                timeper = "Dated"
            info.append(" Num legs: ", input["legs\."])
            info.append(HTMLgen.BR())
        else:
            print "Failed to find input info"

        # Info from the 'rules' file
        interestingParametersFound = {}
        inter = { "num_col_gen_objective_components" : { 'val': None, 'text': "Cost components" },
                  "num_col_gen_resource_components" : { 'val': None, 'text': "Resources components" }}
        ruleFile = os.path.join(subplanDir, "APC_FILES", "rules")
        if os.path.isfile(ruleFile):
            for line in open(ruleFile).xreadlines():
                items = line.split()
                parameter = items[0].split(".")[-1]
                if inter.has_key(parameter):
                    inter[parameter]["val"] = items[1]
                if self.interestingParameters.count(parameter) > 0:
                    interestingParametersFound[parameter] = items[1]

            for item in inter.keys():
                entry = inter[item]
                if entry["val"]:
                    info.append(entry["text"] + ": " + entry["val"] + " ")
                else:
                    info.append(entry["text"] + ": 0 ")

        if group:
            self.currentSuitePage["group"][group]["info"] = info
            self.currentSuitePage["group"][group]["interestingParameters"] = interestingParametersFound
        return period_start, timeper
    
    def readKPIGroupFile(self, suite):
        self.kpiGroupForTest, self.kpiGroups, scales, self.clientname = apc.readKPIGroupFileCommon(suite)
        self.kpiGroupsList = {}
                
    def setUpSuite(self, suite):
        if suite.name == "picador":
            return
        self.readKPIGroupFile(suite)
        listtoappend = None
        if not self.clientname:
            listtoappend = self.nonClientSuiteList
        else:
            if not self.clientSuiteList.has_key(self.clientname):
                self.clientSuiteList[self.clientname] = []
            listtoappend = self.clientSuiteList[self.clientname]
        # Create page for suite.
        self.currentSuitePage = self.suitePages[suite.name] = { 'suitename': suite.name, 'groupsandtests': {}, 'group': {} }
        self.currentSuite = suite
        listtoappend.append(self.currentSuitePage)
            
    def __call__(self, test):
        self.describe(test)
        title = HTMLgen.Text(test.name)
        self.numberOfTests +=1

        # Add test to index list.
        if self.kpiGroupForTest.has_key(test.name):
            group = self.kpiGroupForTest[test.name]            
        else:
            group = "common"
        # Create group if necessary.
        if not self.currentSuitePage["group"].has_key(group):
            self.currentSuitePage["group"][group] = { 'info': None , 'barcharts': None , 'table': [] , 'profiling': {} , 'rulecheckfailureavg': 0 , 'numtests': 0, 'interestingParameters': None}
            if not group == "common": 
                self.currentSuitePage["groupsandtests"][group] = { 'description': self.extractTestInfo(group, test) }
        if group == "common":
            self.currentSuitePage["groupsandtests"][test.name] = { 'description': self.extractTestInfo(None, test) }

        tableDate = "-"
        tableUncovered = -1
        tableOvercovered = -1
        tableIllegal = -1
        tableCost = 0
        tableRuleChecks = 0
        tableRuleFailures = 0
        logFile = test.getFileName(test.app.getConfigValue("log_file"))
        if not logFile:
            return
        ruleFailureItems = ["Rule checks\.", "Failed due to rule violation\."]
        optRun = optimization.OptimizationRun(test.app,  [ optimization.timeEntryName, optimization.activeMethodEntryName, optimization.dateEntryName, optimization.costEntryName], ["uncovered legs\.", "overcovers", "^\ illegal trips"] + self.definingValues + self.interestingValues + ruleFailureItems, logFile)
        if not len(optRun.solutions) == 0:
            lastSolution = optRun.solutions[-1]
            tableDate = lastSolution["Date"]
            tableCost = lastSolution[optimization.costEntryName]
            if lastSolution.has_key("uncovered legs\."):
                tableUncovered = lastSolution["uncovered legs\."]
            if lastSolution.has_key("overcovers"):
                tableOvercovered = lastSolution["overcovers"]
            if lastSolution.has_key("^\ illegal trips"):
                tableIllegal = lastSolution["^\ illegal trips"]
            # Rule checks
            tableRuleChecks, tableRuleFailures = self.extractFromLastColGenSol(test, optRun.solutions, group)
            avg = 0
            if tableRuleChecks > 0:
                avg = float(tableRuleFailures)/float(tableRuleChecks)
                self.currentSuitePage["group"][group]["rulecheckfailureavg"] += avg
            tableRuleStr = "%d/%d (%.2f)" % (tableRuleChecks, tableRuleFailures, avg)
        else:
            tableRuleStr = "NaN"
            print "Warning, no solution in OptimizationRun!"

        self.extractProfiling(test, group)
        
        # Table
        testPerformance = performance.getTestPerformance(test) / 60 # getTestPerformance is seconds now ...
        testMemory = self.getTestMemory(test)
        if testMemory > 0:
            testMemory = str(testMemory)
        else:
            testMemory = "-"
        tableRow = [ test.name, tableCost, float(int(10*testPerformance))/10, testMemory,
                     tableUncovered, tableOvercovered, tableIllegal, tableRuleStr, tableDate ]
        self.currentSuitePage["group"][group]["table"].append(tableRow)
        self.currentSuitePage["group"][group]["numtests"] += 1
        self.totalCPUtime += testPerformance
    def getTestMemory(self, test):
        return performance.getPerformance(test.getFileName("memory"))
    def extractProfiling(self, test, group):
        lprofFile = os.path.join(self.profilesDir, self.currentSuite.name + "__" + test.name + "_lprof.apc")
        if os.path.isfile(lprofFile):
            if not self.currentSuitePage["group"][group]["profiling"]:
                data = self.currentSuitePage["group"][group]["profiling"] = { 'fcns': {}, 'count': 0 , 'tests': [] , 'ravebc': self.raveBC.createBC("RAVE") }
            else:
                data = self.currentSuitePage["group"][group]["profiling"]

            data["tests"].append(test.name)
            rave = self.lprof.analyze(lprofFile, data)

            tl = [ test.name ]
            for raveFcns in self.lprof.raveFunctions:
                if rave.has_key(raveFcns):
                    tl.append(rave[raveFcns])
                else:
                    tl.append(0)
            self.raveBC.fillData(tl, data["ravebc"].datalist)

    def extractFromLastColGenSol(self, test, solution, group):
        while solution:
            lastSolution = solution.pop()
            if lastSolution["Active method"] == "column generator":
                break
        if not lastSolution["Active method"] == "column generator":
            print "Warning: didn't find last colgen solution!"
            return 0, 0
        
        totTime = int(lastSolution["cpu time"]*60)
        # Skip runs shorter than 2 minutes. 
        if totTime < 2*60:
            return 0, 0
        sum = 0
        tl = [ test.name ]
        for val in self.definingValues + self.interestingValues:
            if lastSolution.has_key(val):
                sum += lastSolution[val]
                tl.append(lastSolution[val])
            else:
                tl.append(0)
        tl.append(totTime - sum)

        # Fill data into barchart
        if self.currentSuitePage["group"][group]["barcharts"]:
            chartabs, chartrel = self.currentSuitePage["group"][group]["barcharts"]
        else:
            self.currentSuitePage["group"][group]["barcharts"] = chartabs, chartrel = self.timeSpentBC.createRelAbsBC()

        chartdata = chartabs.datalist, chartrel.datalist
        self.timeSpentBC.fillDataRelAbs(tl, totTime, chartdata)

        ruleChecks = 0
        ruleFailures = 0
        if lastSolution.has_key("Rule checks\."):
            ruleChecks = lastSolution["Rule checks\."]
        if lastSolution.has_key("Failed due to rule violation\."):
            ruleFailures = lastSolution["Failed due to rule violation\."]
        return ruleChecks, ruleFailures


class PlotKPIGroupsAndGeneratePage(apc.PlotKPIGroups):
    def __init__(self, args = []):
        self.dir = None
        self.plotMem = None
        self.plotTimeDivision = None
        argsRem = copy.deepcopy(args)
        for arg in args:
            if arg.find("d=") != -1:
                self.dir = arg
            if arg.find("mem") != -1:
                self.plotMem = 1
                argsRem.remove(arg)
            if arg.find("timediv") != -1:
                self.plotTimeDivision = 1
                argsRem.remove(arg)
        if not self.dir:
            raise plugins.TextTestError, "No directory specified"
        argsRem.remove(self.dir)
        self.dir = os.path.abspath(os.path.expanduser(self.dir[2:]))
        if not os.path.isdir(self.dir):
            try:
                os.mkdir(self.dir)
            except:
                raise plugins.TextTestError, "Failed to create dir " + self.dir
        apc.PlotKPIGroups.__init__(self, argsRem)
    def __del__(self):
        self.doMemPlot = 0
        self.onlyAverage = 0
        self.timeDivision = 0
        apc.PlotKPIGroups.__del__(self)
        self.onlyAverage = 1
        apc.PlotKPIGroups.__del__(self)
        if self.plotMem:
            self.onlyAverage = 0
            self.doMemPlot = 1
            apc.PlotKPIGroups.__del__(self)
        if self.plotTimeDivision:
            self.doMemPlot = 0
            self.timeDivision = 1
            apc.PlotKPIGroups.__del__(self)
        # Now generate a simple HTML doc, if there is anything to document.
        if len(self.groupsToPlot) == 0:
            return
        doc = HTMLgen.SimpleDocument(title="")
        introFile = os.path.join(self.dir, "intro.html")
        if os.path.isfile(introFile):
            doc.append_file(introFile)
        table = HTMLgen.TableLite(border=2, cellpadding=4, cellspacing=1,width="100%")
        for group in self.allGroups:
            numCols = 2
            if self.plotMem:
                numCols += 1
            if self.plotTimeDivision:
                numCols += 1
            table.append(HTMLgen.TR() + [HTMLgen.TH("KPI group " + group, colspan = numCols)])
            plotRow = [ HTMLgen.TD(HTMLgen.Image(self.getPlotName(group, 0, 0, 0, None))),
                        HTMLgen.TD(HTMLgen.Image(self.getPlotName(group, 1, 0, 0, None)))]
            if self.plotMem:
                plotRow.append(HTMLgen.TD(HTMLgen.Image(self.getPlotName(group, 0, 1, 0, None))))
            if self.plotTimeDivision:
                plotRow.append(HTMLgen.TD(HTMLgen.Image(self.getPlotName(group, 0, 0, 1, None))))
            table.append(HTMLgen.TR() + plotRow)
        doc.append(table)
        doc.append(HTMLgen.Heading(5, "Generated by " + string.join(sys.argv)))
        doc.write(os.path.join(self.dir, "index.html"))

    def __repr__(self):
        return "Generating plots and HTML info for"
        
    def setExtraOptions(self, optionGroup, group):
        optionGroup.setValue("av", not self.onlyAverage)
        optionGroup.setValue("oav", self.onlyAverage)
        optionGroup.setValue("pc", 1)
        optionGroup.setValue("p", self.getPlotName(group, self.onlyAverage, self.doMemPlot, self.timeDivision))
        optionGroup.setValue("terminal", "png")
        if optionGroup.getOptionValue("engine") == "mpl":
            optionGroup.setValue("size", "5,5")
        else:
            optionGroup.setValue("size", "0.65,0.65")
        optionGroup.setValue("olav", 1)
        if self.doMemPlot:
            optionGroup.setValue("i", "memory")
            optionGroup.setValue("per", 0)
            optionGroup.setValue("yr", "0:")
            optionGroup.setValue("title", "Memory")
        elif self.timeDivision:
            pass
        elif self.onlyAverage:
            optionGroup.setValue("title", "Average")
        else:
            optionGroup.setValue("title", "Individual")            
    def getPlotName(self, group, average, mem, timediv, fullPath = 1):
        if mem:
            plotName = group + "_mem" + ".png"
        elif timediv:
             plotName = group + "_timediv" + ".png"
        else:
            plotName = group + str(average) + ".png"
        if fullPath:
            return os.path.join(self.dir, plotName)
        else:
            return plotName

        
class ExtractFromStatusFileHTML(apc.ExtractFromStatusFile):
    def __init__(self, args):
        self.comparisonPage = "comparison.html"
        argstoparent = []
        for ar in args:
           flag, val = ar.split("=")
           if flag == "d":
               self.comparisonPage = val
           else:
               argstoparent.append(ar)
        apc.ExtractFromStatusFile.__init__(self, argstoparent)
        self.doc = HTMLgen.SimpleDocument(title="")
        self.table = HTMLgen.TableLite(border=1, cellpadding=1, cellspacing=1,width="100%")
        # Configuration
        self.colors = {'BAD': 'TOMATO', 'ACCEPTABLE': 'LIGHTYELLOW', 'GOOD': 'LIMEGREEN', 'SUPERB': 'LIME' }
        
        execTime = [(-20.0,100000,"BAD"), (-30.0,-20.0, "ACCEPTABLE"), (-50,-30,"GOOD"), (-100000.0,-50,"SUPERB") ]
        cpuTime = [(20,100000000,"BAD"), (10,20, "ACCEPTABLE"), (0,10,"GOOD"), (-100000,0,"SUPERB") ]
        self.coloring = { 'Network generation exec time': execTime,
                          'Generation exec time': execTime,
                          'GT setup exec time': execTime, 
                          'Network generation time': cpuTime,
                          'Generation time': cpuTime,
                          'GT setup time': cpuTime}
    def __del__(self):
        apc.ExtractFromStatusFile.__del__(self)
        self.doc.append(self.table)
        self.doc.write(self.comparisonPage)
    def getColor(self, entry, value):
        if entry in self.coloring.keys() and value != "-":
            for low, high, category in self.coloring[entry]:
                if float(value) >= low and float(value) < high:
                    return self.colors[category]
        return ""
    def formatVersionName(self, origName):
        return origName.replace("_", " ")
    def printCase(self, name, data, dataComp, anyToPrint = True, printMaxMin = False):
        if not anyToPrint:
            return
        row = [ HTMLgen.TD(HTMLgen.Name(name, text=name), bgcolor="LightGray") ]
        for vix in  xrange(len(self.versions)):
            v = self.versions[vix]
            row.append(HTMLgen.TD(self.formatVersionName(v), bgcolor="WhiteSmoke", align = "Center"))
            if vix%2:
                diffCell = HTMLgen.TD("Diff (%)", bgcolor="WhiteSmoke", align = "center")
                if not printMaxMin:
                    row.append(diffCell)
                else:
                    miniTable = HTMLgen.TableLite(border=0, cellpadding=0, cellspacing=0, width="100%")
                    diffCell.__setattr__("colspan", 2)
                    miniTable.append(HTMLgen.TR() + [ diffCell ])
                    miniTable.append(HTMLgen.TR() + [ HTMLgen.TD("Min (%)", bgcolor="WhiteSmoke", align = "center"),
                                                      HTMLgen.TD("Max (%)", bgcolor="WhiteSmoke", align = "center") ])
                    row.append(HTMLgen.TD(miniTable))
        self.table.append(HTMLgen.TR() + row)
        numValues = 0
        for t in self.printValues:
            if numValues % 2:
                defaultBGColor = "GhostWhite"
            else:
                defaultBGColor = ""            
            row = [ HTMLgen.TD(t) ]
            for v in range(len(self.versions)):
               row.append(HTMLgen.TD("%s"%apc.stringify(data[v].get(t,"-")), align = "center"))
               if v%2:
                   comp = dataComp[v/2].get(t,"-")
                   color = self.getColor(t, comp)
                   diffCell = HTMLgen.TD("%s"%apc.stringify(comp), bgcolor = color, align = "center")
                   if not printMaxMin:
                       row.append(diffCell)
                   else:
                       miniTable = HTMLgen.TableLite(border=0, cellpadding=0, cellspacing=0, width="100%")
                       diffCell.__setattr__("colspan", 2)
                       miniTable.append(HTMLgen.TR() + [ diffCell ])
                       mini = self.minCommon[v/2].get(t,"-")
                       maxi = self.maxCommon[v/2].get(t,"-")
                       mintag = "#" + self.minCommonTag[v/2].get(t,"-")
                       maxtag = "#" + self.maxCommonTag[v/2].get(t,"-")
                       miniColor = self.getColor(t, mini)
                       maxiColor = self.getColor(t, maxi)
                       miniTable.append(HTMLgen.TR() + [ HTMLgen.TD(HTMLgen.Href(mintag, "%s"%apc.stringify(mini)), bgcolor = miniColor, align = "center"),
                                                         HTMLgen.TD(HTMLgen.Href(maxtag,"%s"%apc.stringify(maxi)), bgcolor = maxiColor, align = "center") ])
                       row.append(HTMLgen.TD(miniTable))
            self.table.append(HTMLgen.TR(bgcolor = defaultBGColor) + row)
            numValues += 1