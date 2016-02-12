    def Free(self, n, info=False):
        """
        use the uacalculator to compute the free algebra on n gens over self
        """
        st = self.uacalc_format("A"+str(self.index))
        writefile('tmpalgA.ua',st)
        os.system('java -classpath '+clspth+'uacalc/classes/ org.uacalc.example.FreeAlg tmpalgA.ua '+str(n)+' >tmpout.txt')
        st = readfile('tmpout.txt')
        if info: print st
        return int(st[st.find("fr size = ")+10:st.find(" elements")])

