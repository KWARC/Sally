package info.kwarc.sally.networking.cometd;

import java.io.IOException;
import java.util.Set;
import java.util.regex.Pattern;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.reflections.Reflections;
import org.reflections.scanners.ResourcesScanner;
import org.reflections.util.ClasspathHelper;
import org.reflections.util.ConfigurationBuilder;

public class DefaultServlet extends HttpServlet
{
    private String greeting="Hello World";
    public DefaultServlet(){}
    public DefaultServlet(String greeting)
    {
        this.greeting=greeting;
    }
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException
    {
        response.setContentType("text/html");
        response.setStatus(HttpServletResponse.SC_OK);
        response.getWriter().println("<h1>"+greeting+System.getProperty("user.dir")+"</h1>");
        response.getWriter().println("session=" + request.getSession(true).getId());

        Reflections reflections = new Reflections(new ConfigurationBuilder()
		.addUrls(ClasspathHelper.forPackage("sally"))
				.setScanners(new ResourcesScanner()));

		Set<String> propertiesFiles = reflections.getResources(Pattern.compile(".*"));
		response.getWriter().println(propertiesFiles.size());
		for (String file : propertiesFiles) {
			response.getWriter().println(file);
		}
    }
}