
""" Base class for all the queue system implementations """

import subprocess
import plugins

class QueueSystem:
    def submitSlaveJob(self, cmdArgs, slaveEnv, logDir, submissionRules, jobType):
        try:
            process = subprocess.Popen(cmdArgs, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       cwd=logDir, env=slaveEnv)
            stdout, stderr = process.communicate()
            errorMessage = self.findErrorMessage(stderr, cmdArgs, jobType)
        except OSError:
            errorMessage = self.getFullSubmitError("local machine is not a submit host: running '" + cmdArgs[0] + "' failed.", cmdArgs, jobType)
        if errorMessage:
            return None, errorMessage
        else:
            return self.findJobId(stdout), None

    def supportsPolling(self):
        return True

    def findErrorMessage(self, stderr, *args):
        if len(stderr) > 0:
            basicError = self.findSubmitError(stderr)
            if basicError:
                return self.getFullSubmitError(basicError, *args)
            
    def getFullSubmitError(self, errorMessage, cmdArgs, jobType):
        qname = self.getQueueSystemName()
        err = "Failed to submit "
        if jobType:
            err += jobType + " "
        err += "to " + qname + " (" + errorMessage.strip() + ")\n" + \
               "Submission command was '" + self.formatCommand(cmdArgs) + "'\n"
        return err

    def getQueueSystemName(self):
        modname = self.__class__.__module__
        return modname.split(".")[-1].upper()

    def addExtraAndCommand(self, args, submissionRules, commandArgs):
        args += submissionRules.getExtraSubmitArgs()
        if commandArgs:
            args.append(self.shellWrap(commandArgs))
        return args

    def formatCommand(self, cmdArgs):
        return " ".join(cmdArgs[:-1]) + " ... "
        
    def getSubmitCmdArgs(self, submissionRules, commandArgs=[]):
        return commandArgs

    def getJobFailureInfo(self, jobId):
        name = self.getQueueSystemName()
        header = "-" * 10 + " Full accounting info from " + name + " " + "-" * 10 + "\n"
        if jobId is None:
            return header + "No job has been submitted to " + name
        else:
            return header + self._getJobFailureInfo(jobId)
                   
    def shellWrap(self, commandArgs):
        # Must use exec so as not to create extra processes: SGE's qdel isn't very clever when
        # it comes to noticing extra shells
        return "exec $SHELL -c \"exec " + plugins.commandLineString(commandArgs) + "\"" if commandArgs else ""
