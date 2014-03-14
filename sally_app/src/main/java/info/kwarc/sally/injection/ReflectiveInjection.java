package info.kwarc.sally.injection;

import org.reflections.Reflections;
import org.xeustechnologies.jcl.JarClassLoader;
import org.xeustechnologies.jcl.JclObjectFactory;

import java.io.File;
import java.lang.reflect.Method;
import java.net.*;
import java.util.Set;
import java.util.jar.*;

public class ReflectiveInjection {
	
	static Reflections reflections;
	
	public static void main(String[] args){
		String path = "C:\\temp\\" ; //example
		URL url;
		try {
			url = new File(path).toURI().toURL();
			JarClassLoader_Ex jarClassLoader = new JarClassLoader_Ex(url);
			//jarClassLoader.in
		} catch (MalformedURLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		//This one recursively loads all the jar files from a directory.
		JarClassLoader jcl = new JarClassLoader();
		jcl.add("serviceplugins/"); //example path, adds recursively from subfolders too 
		
		//Create default factory
		  JclObjectFactory factory = JclObjectFactory.getInstance();
		
		//Create object of loaded class
		  Object obj = factory.create(jcl,"info.kwarc.sally.core.SallyService");
		  Set<Method> services =      reflections.getMethodsAnnotatedWith(info.kwarc.sally.core.SallyService.class);
		  //Obtain interface reference in the current classloader
		  //SallyService ss = JclUtils.cast(obj, SallyService.class);
		
	}
}
