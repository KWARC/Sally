package info.kwarc.sally.core.theo;


public interface IPositionProvider {
	Coordinates getRecommendedPosition();
	void setRecommendedCoordinates(Coordinates pos);
}
