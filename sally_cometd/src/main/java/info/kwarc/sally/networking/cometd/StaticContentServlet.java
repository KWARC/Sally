package info.kwarc.sally.networking.cometd;

import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.Set;
import java.util.regex.Pattern;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.apache.commons.io.FileUtils;
import org.reflections.Reflections;
import org.reflections.scanners.ResourcesScanner;
import org.reflections.util.ClasspathHelper;
import org.reflections.util.ConfigurationBuilder;

public class StaticContentServlet extends HttpServlet
{
	Set<String> filesToServe;

	public StaticContentServlet() {
		Reflections reflections = new Reflections(new ConfigurationBuilder()
		.addUrls(ClasspathHelper.forPackage("sally/web"))
		.setScanners(new ResourcesScanner()));

		filesToServe = reflections.getResources(Pattern.compile(".*"));
		for (String s : filesToServe) {
			System.out.println(s);
		}
	}

	void genMsg(int code, String message, HttpServletResponse response) {
		response.setContentType("text/html");
		response.setStatus(code);
		try {
			response.getWriter().println("<h1>"+message+"</h1>");
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException
	{
		String path = request.getPathInfo();
		String normalized;
		try {
			normalized = new URI(path).normalize().getPath();
		} catch (URISyntaxException e) {
			genMsg(HttpServletResponse.SC_BAD_REQUEST, "Invalid request path.", response);
			return;
		}

		if (normalized.equals("/"))
			normalized = "/index.html";
		normalized = "sally/web"+normalized;
		System.out.println("requested " +normalized);

		if (filesToServe.contains(normalized)) {
			if (normalized.endsWith("js")) {
				response.setContentType("application/javascript");
			} else {
				response.setContentType("text/html");
			}
			response.setStatus(HttpServletResponse.SC_OK);
			String xml = FileUtils.readFileToString(
					FileUtils.toFile(
							this.getClass().getResource("/"+normalized)
							)
					);
			response.getWriter().write(xml);
			return;
		}
		genMsg(HttpServletResponse.SC_NOT_FOUND, "No file found.", response);		
	}
}